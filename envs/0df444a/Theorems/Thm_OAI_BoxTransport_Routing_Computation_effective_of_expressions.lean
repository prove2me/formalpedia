-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_Computation_effective_of_expressions
-- name    : OAI.BoxTransport.Routing.Computation.effective_of_expressions
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:26:41.270312+00:00
-- url     : https://prove2.me/theorems/58115884-6ddf-4b37-8ccd-12644acde640
-- title:
--   Smooth compactly supported fields with valid closed-form components are effective
-- statement:
--   Let $U:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ be a time-dependent vector field on space-time. Points are written $p=(t,x)$ with $x=(x_0,x_1,x_2)$, and space-time carries the sup norm $\|(t,x)\|=\max(|t|,|x_0|,|x_1|,|x_2|)$.
--
--   **Expressions.** An *expression* is a finite tree built from the four variables $t,x_0,x_1,x_2$ by sums $e+f$, products $e\cdot f$, negation $-e$, and unary nodes carrying a natural-number label $m$: for $m=3k$ the node is a rational constant (the label encodes the rational, and every rational occurs), for $m=3b+1$ it is the reciprocal $1/e$, and for $m=3k+2$ it is $\varphi_k(e)$, where
--   $$\varphi_k(s)=s^{-k}\exp(-1/s)\ \ (s>0),\qquad \varphi_k(s)=0\ \ (s\le 0).$$
--   Each expression $e$ denotes a function $f_e:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}$ in the evident way. It is *valid* if every reciprocal node $1/e'$ occurring in it, with label $3b+1$, has its denominator bounded away from zero by the label: $|f_{e'}(p)|\ge 1/(b+1)$ for all $p$.
--
--   **Effectivity.** An *axis* is one of: time, $0$, $1$, $2$. For a finite list $D=(d_1,\dots,d_k)$ of axes put $\partial_D U=\partial_{d_1}\partial_{d_2}\cdots\partial_{d_k}U$ (the empty list gives $U$ itself). A rational number is coded by a triple $(a,b,c)\in\mathbb{N}^3$ with value $(a-b)/(c+1)$, and a rational space-time point by four such triples; write $\bar q\in\mathbb{R}\times\mathbb{R}^3$ for the point coded by $q$. The field $U$ is called *effective* if there are computable maps $\mathrm{ev}$ (returning a rational code), $\mu$ and $B$ (returning natural numbers) such that for every list of axes $D$, every coded point $q$, every $n\in\mathbb{N}$, every $p\in\mathbb{R}\times\mathbb{R}^3$ and every $j\in\{0,1,2\}$,
--   $$\|p-\bar q\|\le\frac{1}{\mu(D,n)+1}\ \Longrightarrow\ \bigl|(\partial_DU)_j(p)-\mathrm{ev}(D,q,n,j)\bigr|\le\frac{1}{n+1},\qquad\text{and}\qquad \bigl|(\partial_DU)_j(p)\bigr|\le B(D).$$
--
--   **Theorem.** Assume $U$ is $C^\infty$ and has compact support, and that there are valid expressions $e_0,e_1,e_2$ with
--   $$f_{e_j}(p)=U_j(p)\qquad\text{for all }p\in\mathbb{R}\times\mathbb{R}^3\text{ and }j\in\{0,1,2\}.$$
--   Then $U$ is effective.
--
--   The theorem reduces effectivity, a computability property of all mixed derivatives at once (rational approximations at rational points with computable moduli of continuity, plus computable uniform bounds), to writing the three components of a smooth compactly supported field as valid closed-form expressions. Such expressions cover rational polynomials in $t$ and $x$, quotients by functions bounded away from zero, and the usual smooth cut-off and transition functions built from $\exp(-1/s)$; this is how the explicitly constructed vector fields of the box-routing construction are shown to be effective.
--
--   **Formalization Note** Expressions reuse Mathlib's inductive type `Nat.Partrec.Code` purely as a countable syntax with primitive-recursive recursion: `zero`, `succ`, `left`, `right` stand for $t,x_0,x_1,x_2$, `pair` is the sum, `comp` the product, `rfind'` negation, and `prec m e` is the unary node with label `Encodable.encode m` (a constant node ignores its argument, which must nevertheless be valid). The constant with label $3k$ is `Qval (Denumerable.ofNat QCode k)`, and $\varphi_k$ is `flatTerm k`, i.e. $s^{-k}$ times Mathlib's `expNegInvGlue`. Iterated derivatives are `mixedDerivative`, defined through `fderiv` applied to coordinate unit vectors, with the head of the list as the outermost derivative. Computability is Mathlib's `Computable` for the standard encodings of lists of axes (`Option (Fin 3)`), natural numbers, products and `Fin 3`, and the space-time norm is Lean's max norm on the product of $\mathbb{R}$ with $\mathbb{R}^3$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Expressions.lean#L730-L770

import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Definitions.Def_OAI_Analysis_BoxTransport_Computation
import Definitions.Def_OAI_Analysis_BoxTransport_Expressions

open OAI OAI.BoxTransport OAI.BoxTransport.Routing OAI.BoxTransport.Routing.Computation
open scoped Topology
open scoped BigOperators ContDiff
open scoped BigOperators ContDiff
open Nat.Partrec
open scoped BigOperators ContDiff
open Nat.Partrec
open scoped BigOperators ContDiff
open Nat.Partrec
open scoped BigOperators ContDiff
open Nat.Partrec

theorem OAI.BoxTransport.Routing.Computation.effective_of_expressions {U : Field} (hU : ContDiff ℝ ∞ U) (hc : HasCompactSupport U)
    (es : Fin 3 → Expr) (he : ∀ j, Valid (es j)) (hval : ∀ p j, value (es j) p = U p j) :
    Effective U := by sorry
