-- Prove2me | Theorems.Thm_OAI_BoxTransport_Routing_Computation_value_bound
-- name    : OAI.BoxTransport.Routing.Computation.value_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T13:24:13.487857+00:00
-- url     : https://prove2.me/theorems/37177cc9-b130-44c4-88d6-006b4e6704d1
-- title:
--   A priori bounds for the values of valid smooth expressions on a cube of radius $R$
-- statement:
--   **Expressions.** A triple $(p,r,d)\in\mathbb{N}^3$ codes the rational number $(p-r)/(d+1)$, and $q_\mu$ denotes the code numbered $\mu\in\mathbb{N}$ under a fixed enumeration of $\mathbb{N}^3$. For $\mu\in\mathbb{N}$ let $\phi_\mu(y)=y^{-\mu}e^{-1/y}$ for $y>0$ and $\phi_\mu(y)=0$ for $y\le0$. Expressions are finite trees built from the four leaves $T,X_1,X_2,X_3$, sums $e+f$, products $e\cdot f$, negations $-e$, and unary nodes $\langle k\rangle e$ labelled by $k\in\mathbb{N}$. With $\mu=\lfloor k/3\rfloor$, the node $\langle k\rangle e$ means: the rational constant with code $q_\mu$ (ignoring $e$) if $k\equiv0\pmod 3$; the reciprocal $1/e$ with guard $\mu$ if $k\equiv1\pmod 3$; and the flat function $\phi_\mu(e)$ if $k\equiv2\pmod 3$. The value of $e$ is the function $e(t,x)$ on $\mathbb{R}\times\mathbb{R}^3$ obtained by reading $T,X_1,X_2,X_3$ as $t,x_1,x_2,x_3$. An expression is *valid* if below every reciprocal node with guard $\mu$ the subexpression $e$ satisfies $|e(t,x)|\ge1/(\mu+1)$ for all $(t,x)$.
--
--   **Bounds.** For $R\in\mathbb{N}$ define $B_R(e)\in\mathbb{N}$ recursively: $B_R=R$ on each leaf; $B_R(e+f)=B_R(e)+B_R(f)$; $B_R(e\cdot f)=B_R(e)\,B_R(f)$; $B_R(-e)=B_R(e)$; and $B_R=p+r$ for a constant with code $q_\mu=(p,r,d)$, $B_R=\mu+1$ for a reciprocal with guard $\mu$, $B_R=\mu!$ for a flat node $\phi_\mu$.
--
--   **Theorem.** Let $e$ be a valid expression, $R\in\mathbb{N}$, and $(t,x)\in\mathbb{R}\times\mathbb{R}^3$ with $\|(t,x)\|=\max(|t|,|x_1|,|x_2|,|x_3|)\le R$. Then
--
--   $$|e(t,x)|\le B_R(e).$$
--
--   The bound $B_R(e)$ is computed from the syntax of $e$ alone and controls the expression uniformly on the cube of radius $R$. It is needed when approximation errors are propagated through products in the exact-rational evaluation of expressions.
--
--   **Formalization Note** Expressions are `Expr := Nat.Partrec.Code`, with `zero`, `succ`, `left`, `right` as the leaves $T,X_1,X_2,X_3$, `pair` as sum, `comp` as product, `rfind'` as negation and `prec m e` as the unary node with label `Encodable.encode m`; $q_\mu$ is `Denumerable.ofNat QCode μ`. $B_R$ is `boundE R`, the value is `value e`, and the norm on `SpaceTime` is the product of sup norms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Expressions.lean#L295-L318

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

theorem OAI.BoxTransport.Routing.Computation.value_bound {e : Expr} (he : Valid e) (R : ℕ) {p : SpaceTime} (hp : ‖p‖ ≤ R) :
    |value e p| ≤ boundE R e := by sorry
