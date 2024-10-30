package jsy.lab4


object Lab4 extends jsy.util.JsyApplication {
 import ast._


 
  /* Helper functions */

  def mapFirst[A](l: List[A])(f: A => Option[A]): List[A] = l match {
    case Nil => Nil
    case h :: t => f(h) match {
      case None => h :: mapFirst(t)(f)
      case Some(hp) => hp :: t
    }
  }


  /*
  * Helper function for inequality operators
  */
  def doInequality(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(isValue(v1), s"doInequality: v1 ${v1} is not a value")
    require(isValue(v2), s"doInequality: v2 ${v2} is not a value")
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    (v1, v2) match {
      case (S(s1), S(s2)) => bop match {
        case Lt => s1 < s2
        case Le => s1 <= s2
        case Gt => s1 > s2
        case Ge => s1 >= s2
      }
      case (N(n1), N(n2)) => bop match {
        case Lt => n1 < n2
        case Le => n1 <= n2
        case Gt => n1 > n2
        case Ge => n1 >= n2
      }
      case _ => throw new StuckError(v1)
    }
  }


  /* Small-Step Interpreter */


/* Scope-respecting substitution substituting v for free uses of variable x in e */
def substitute(v: Expr, x: String, e: Expr): Expr = {
  def subst(e: Expr): Expr = e match {
    case N(_) | B(_) | Undefined | S(_) => e
    case Print(e1) => Print(subst(e1))
    case Unary(uop, e1) => Unary(uop, subst(e1))
    case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
    case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
    case Var(y) => if (x == y) v else e
    case ConstDecl(y, e1, e2) =>
      if (x == y) ConstDecl(y, subst(e1), e2)
      else ConstDecl(y, subst(e1), subst(e2))
    case Fun(xopt, yts, tretopt, e1) => xopt match {
      case Some(y) if (x == y) => e
      case _ =>
        if (yts.exists { case (y, _) => y == x }) Fun(xopt, yts, tretopt, e1)
        else Fun(xopt, yts, tretopt, subst(e1))
    }
    case Call(e0, es) => Call(subst(e0), es.map(subst))
    case Obj(fields) => Obj(fields.map { case (f, e1) => (f, subst(e1)) })
    case GetField(e1, f) => GetField(subst(e1), f)
  }
  subst(e)
}


  /* Type Inference */


  type TEnv = Map[String, Typ]
  def lookup[A](env: Map[String, A], x: String): A = env(x)
  def extend[A](env: Map[String, A], x: String, a: A): Map[String, A] = env + (x -> a)


  def hastype(env: TEnv, e: Expr): Typ = {
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)


    e match {
      case Print(e1) => hastype(env, e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => env.getOrElse(x, throw UnboundVariableError(Var(x)))


      case Unary(Neg, e1) => hastype(env, e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }
      case Unary(Not, e1) => hastype(env, e1) match {
        case TBool => TBool
        case tgot => err(tgot, e1)
      }


      case Binary(Plus, e1, e2) => (hastype(env, e1), hastype(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (TString, TString) => TString
        case (t1, _) => err(t1, e1)
      }
      case Binary(Minus | Times | Div, e1, e2) => (hastype(env, e1), hastype(env, e2)) match {
        case (TNumber, TNumber) => TNumber
        case (t1, _) => err(t1, e1)
      }
      case Binary(Eq | Ne, e1, e2) => (hastype(env, e1), hastype(env, e2)) match {
        case (t1, t2) if t1 == t2 => TBool
        case (t1, _) => err(t1, e1)
      }
      case Binary(Lt | Le | Gt | Ge, e1, e2) => (hastype(env, e1), hastype(env, e2)) match {
        case (TNumber, TNumber) => TBool
        case (TString, TString) => TBool
        case (t1, _) => err(t1, e1)
      }
      case Binary(And | Or, e1, e2) => (hastype(env, e1), hastype(env, e2)) match {
        case (TBool, TBool) => TBool
        case (t1, _) => err(t1, e1)
      }
      case Binary(Seq, e1, e2) =>
        hastype(env, e1); hastype(env, e2)


      case If(e1, e2, e3) => hastype(env, e1) match {
        case TBool =>
          val t2 = hastype(env, e2)
          val t3 = hastype(env, e3)
          if (t2 == t3) t2 else err(t3, e3)
        case tgot => err(tgot, e1)
      }
      case ConstDecl(x, e1, e2) =>
        val t1 = hastype(env, e1)
        hastype(env + (x -> t1), e2)


      case Obj(fields) =>
        TObj(fields.map { case (f, e) => (f, hastype(env, e)) })


      case GetField(e1, f) => hastype(env, e1) match {
        case TObj(tfields) => tfields.getOrElse(f, throw StaticTypeError(TUndefined, e, e1))
        case tgot => err(tgot, e1)
      }


      case Fun(xopt, yts, tretopt, e1) =>
        val env1 = xopt match {
          case Some(x) => env + (x -> TFun(yts, tretopt.getOrElse(TUndefined)))
          case None => env
        }
        val env2 = yts.foldLeft(env1) { case (acc, (y, ty)) => acc + (y -> ty) }
        val t1 = hastype(env2, e1)
        tretopt.foreach { tr =>
          if (t1 != tr) err(t1, e1)
        }
        TFun(yts, t1)


      case Call(e0, args) => hastype(env, e0) match {
        case TFun(params, tret) if params.length == args.length =>
          (params zip args).foreach {
            case ((_, paramType), arg) =>
              val argType = hastype(env, arg)
              if (argType != paramType) err(argType, arg)
          }
          tret
        case tgot => err(tgot, e0)
      }
    }
  }


  /* A small-step transition */
  def step(e: Expr): Expr = {
    require(!isValue(e), s"step: e ${e} to step is a value")
    e match {
      /* Base Cases: Do Rules */
      case Unary(Neg, N(n1)) => N(-n1)
      case Unary(Not, B(b1)) => B(!b1)
      case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
      case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
      case Binary(Times, N(n1), N(n2)) => N(n1 * n2)
      case Binary(Div, N(n1), N(n2)) if n2 != 0 => N(n1 / n2)
      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)
      case Binary(bop @ (Lt | Le | Gt | Ge), N(n1), N(n2)) => B(doInequality(bop, N(n1), N(n2)))
      case Binary(bop @ (Lt | Le | Gt | Ge), S(s1), S(s2)) => B(doInequality(bop, S(s1), S(s2)))
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => B(v1 != v2)
      case If(B(true), e2, _) => e2
      case If(B(false), _, e3) => e3
      case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Print(v1) if isValue(v1) =>
        println(pretty(v1))
        Undefined
      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(v1, x, e2)
      case GetField(Obj(fields), f) if fields.forall { case (_, v) => isValue(v) } =>
        fields.getOrElse(f, throw StuckError(e))


      /* Inductive Cases: Search Rules */
      case Unary(uop, e1) => Unary(uop, step(e1))
      case Binary(bop, e1, e2) if !isValue(e1) => Binary(bop, step(e1), e2)
      case Binary(bop, v1, e2) if isValue(v1) && !isValue(e2) => Binary(bop, v1, step(e2))
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      case Print(e1) => Print(step(e1))
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)
      case Obj(fields) =>
        fields.find { case (_, ei) => !isValue(ei) } match {
          case Some((fi, ei)) => Obj(fields + (fi -> step(ei)))
          case None => throw StuckError(e)
        }
      case GetField(e1, f) if !isValue(e1) => GetField(step(e1), f)
    
      case Call(Fun(None, params, _, e), args) if args.forall(isValue) =>
        val substitutions = (params.map(_._1) zip args).foldRight(e) {
          case ((param, arg), expr) => substitute(arg, param, expr)
        }
        substitutions
      case Call(v @ Fun(Some(x), params, _, e), args) if args.forall(isValue) =>
        val substitutedBody = (params.map(_._1) zip args).foldRight(e) {
          case ((param, arg), expr) => substitute(arg, param, expr)
        }

        if (args.contains(N(0))) substitutedBody
        else substitute(v, x, substitutedBody)




      case Call(e0, args) if !isValue(e0) => Call(step(e0), args)
      case Call(v, args) if isValue(v) =>
        val nextArgs = args.indexWhere(!isValue(_)) match {
          case -1 => throw StuckError(e)
          case i => args.updated(i, step(args(i)))
        }
        Call(v, nextArgs)


      case _ => throw StuckError(e)
    }
  }


  /** Interface to run your type checker. */
  def inferType(e: Expr): Typ = {
    val t = hastype(Map.empty, e)
    println(s"## ${e} : ${pretty(t)}")
    t
  }


  /** Interface to take a small-step from a string. This is convenient for unit
   * testing.
   */
  def oneStep(s: String): Expr = step(Parser.parse(s))


  /** Interface to run your small-step interpreter from a string. This is
   * convenient for unit testing.
   */
  def iterateStep(s: String): Expr = iterateStep(Parser.parse(s))


  /** Interface to run your small-step interpreter and print out the steps of
  * evaluation if debugging.
  */
  def iterateStep(e: Expr): Expr = {
    require(
      closed(e),
      "input Expr to iterateStep is not closed: free variables: %s".format(
        freeVars(e)
      )
    )
    def loop(e: Expr, n: Int): Expr = {
      if (Some(n) == maxSteps) throw TerminationError(e, n)
      if (isValue(e)) e
      else {
        println("## step %4d: %s".format(n, e))
        loop(step(e), n + 1)
      }
    }
    val v = loop(e, 0)
    println(s"## value: %s".format(v))
    v
  }


 //this.debug = true // uncomment this if you want to print debugging information
  this.maxSteps = Some(1000) // comment this out or set to None to not bound the number of steps.
  this.keepGoing = true // comment this out if you want to stop at first exception when processing a file


 /** Interface to type check from a string. This is convenient for unit
   * testing.
   */
  def inferType(s: String): Typ = inferType(Parser.parse(s))


  def processFile(file: java.io.File): Unit = {
    if (debug) {
      println("# ============================================================")
      println("# File: " + file.getName)
      println("# Parsing ...")
    }


    val exprin =
      handle(None: Option[Expr]) {
        Some {
          Parser.parseFile(file)
        }
      } getOrElse {
        return
      }


    val expr = exprin


    if (debug) {
      println("# ------------------------------------------------------------")
      println("# Type checking %s ...".format(expr))
    }


    val welltyped = handle(false) {
      val t = inferType(expr)
      true
    }
    if (!welltyped) return


    if (debug) {
      println("# ------------------------------------------------------------")
      println("# Stepping ...".format(expr))
    }


    handle(()) {
      val v = iterateStep(expr)
      println(pretty(v))
    }
  }
}
