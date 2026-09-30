-- Prove2me | Theorems.Thm_NonsmoothNewton_Shared_bJac_mem_of_tendsto
-- name    : NonsmoothNewton.Shared.bJac_mem_of_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-29T21:34:29.11773+00:00
-- url     : https://prove2.me/theorems/0f8c1bb3-1d72-4b7d-ba72-e6fffbc5c2a9
-- title:
--   The B-Jacobian has a sequentially closed graph
-- statement:
--   Let $F : E \to G$ be a map between finite-dimensional real normed spaces, and write $\partial_B F(y)$ for the B-limit set `bJac F y`, i.e. the set of limits of the Fréchet derivatives of $F$ along sequences of differentiability points converging to $y$.
--
--   If $(x_k)$ converges to $x$, if $(V_k)$ converges to an operator $V$, and if $V_k \in \partial_B F(x_k)$ for every $k$, then $V \in \partial_B F(x)$. In words, the B-limit sets have a sequentially closed graph: no new B-limit element can appear in the limit of a convergent sequence of B-limit elements.
--
--   **Formalization Note** `bJac F y` unfolds to the existence of a sequence $u : \mathbb{N} \to E$ with $u n \to y$, each $u n$ a point of differentiability of $F$, and $F'(u n) \to V$. The proof is diagonal: for each $k$ it extracts a late term of the witness sequence for $V_k$ whose two errors (in position and in derivative) are both below $1/(k+1)$. The resulting sequence satisfies $z_k \to x$ and $F'(z_k) \to V$ by the triangle inequality, since $1/(k+1) \to 0$. No Lipschitz or measurability assumption on $F$ is required.
-- source:
--   Qi, Sun, A nonsmooth version of Newton's method, Math. Programming 58 (1993), Section 3, p. 354. Sequential closed graph of the B-limit (Bouligand) set, used to pass pointwise invertibility of the generalized Jacobian to a uniform inverse-norm bound over a neighbourhood.

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
open Filter Topology Set

namespace NonsmoothNewton.Shared

/-- The graph of the B-limit set `bJac F` is sequentially closed.

If `xseq` converges to `x`, if `Vseq` converges to `V`, and if each `Vseq k` lies in
`bJac F (xseq k)`, then `V` lies in `bJac F x`. This is the closed-graph (upper
semicontinuity) ingredient that turns a pointwise invertibility statement into a
uniform inverse-norm bound over a neighbourhood: any accumulation point of
generalized Jacobians along a convergent sequence of base points is again a
generalized Jacobian of the limit.

The proof is a diagonal argument. For each `k` the membership hypothesis supplies a
differentiability sequence converging to `xseq k` with derivatives converging to
`Vseq k`. Choosing one sufficiently late term of each such sequence, with both
errors below `1/(k+1)`, produces a single sequence converging to `x` whose
derivatives converge to `V`. No regularity of `F` is needed. -/
theorem bJac_mem_of_tendsto {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    {F : E → G} {x : E} {xseq : ℕ → E}
    {Vseq : ℕ → E →L[ℝ] G} {V : E →L[ℝ] G}
    (hx : Tendsto xseq atTop (𝓝 x))
    (hV : Tendsto Vseq atTop (𝓝 V))
    (hmem : ∀ k, Vseq k ∈ bJac F (xseq k)) :
    V ∈ bJac F x := by sorry

end NonsmoothNewton.Shared
