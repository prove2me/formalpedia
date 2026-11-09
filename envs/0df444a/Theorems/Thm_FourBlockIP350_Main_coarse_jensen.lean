-- Prove2me | Theorems.Thm_FourBlockIP350_Main_coarse_jensen
-- name    : FourBlockIP350.Main.coarse_jensen
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:26.199901+00:00
-- url     : https://prove2.me/theorems/c993a9ed-33c1-4727-a7a9-d063cb580807
-- title:
--   Claim 4.2.3 — Jensen inequality on the coarser lattice
-- statement:
--   Let $k\ge1$ and let $h:\mathbb Z^k\to\mathbb R$ be everywhere finite and midpoint-convex. For any finite list $p_0,\ldots,p_a\in k\mathbb Z^k$ and nonnegative real weights with sum one, if $z=\sum_i\lambda_i p_i$ also belongs to $k\mathbb Z^k$, then
--   $$h(z)\le\sum_{i=0}^a\lambda_i h(p_i).$$
--   Neither affine independence nor rationality of the weights is required. This is the full finite-combination inequality used to define the envelope.
--
--   Differences from the source: none.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 11, Claim 4.2.3

import Mathlib
import Definitions.Def_FourBlockIP350_Main_LatticeConvexity

namespace FourBlockIP350.Main

open scoped BigOperators

theorem coarse_jensen {k a : ℕ} (hk : 0 < k) (h : ZVec k → ℝ)
    (hh : MidpointConvex h) (p : Fin (a+1) → ZVec k)
    (hp : ∀ i, p i ∈ CoarseLattice k) (lam : Fin (a+1) → ℝ)
    (hlam : ∀ i, 0 ≤ lam i) (hsum : ∑ i, lam i = 1)
    (z : ZVec k) (hz : z ∈ CoarseLattice k)
    (hrep : (∑ i, lam i • realVec (p i)) = realVec z) :
    h z ≤ ∑ i, lam i * h (p i) := by sorry

end FourBlockIP350.Main
