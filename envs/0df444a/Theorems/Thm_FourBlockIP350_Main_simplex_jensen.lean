-- Prove2me | Theorems.Thm_FourBlockIP350_Main_simplex_jensen
-- name    : FourBlockIP350.Main.simplex_jensen
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:04.761288+00:00
-- url     : https://prove2.me/theorems/84f11496-1062-4289-8dd6-2fb2d8fb10c0
-- title:
--   Claim 4.2.2 — Jensen inequality on a simplex
-- statement:
--   Let $h$ be everywhere finite and midpoint-convex, and let $P=\operatorname{conv}\{kp_0,\ldots,kp_r\}$ be a simplex as in Claim 4.2.1. If $A$ is affine on the affine span of $P$ and agrees with $h$ at every vertex, then
--   $$h(w)\le A(w)\qquad(w\in P\cap\mathbb Z^k).$$
--   The restriction concerns every integer point of the simplex, including those outside the coarser lattice. This supplies the simplex form of Jensen's inequality.
--
--   Differences from the source:
--   - encoding: A is the affine interpolant on aff(P) agreeing with h at the vertices → simplexInterpolant is constructed from h and the vertices using their unique affine coordinates; reason: affine independence guarantees the unique interpolant on the affine span; arbitrary values outside that span are never used, and no independent A is assumed
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 10, Claim 4.2.2

import Mathlib
import Definitions.Def_FourBlockIP350_Main_LatticeConvexity

namespace FourBlockIP350.Main

open scoped BigOperators

theorem simplex_jensen {k r : ℕ} (hk : 0 < k) (hr : r ≤ k)
    (h : ZVec k → ℝ) (hh : MidpointConvex h)
    (p : Fin (r+1) → ZVec k) (hp : IndependentPoints p) :
    ∀ w : ZVec k, realVec w ∈ DilatedSimplex p →
      h w ≤ simplexInterpolant h p (realVec w) := by sorry

end FourBlockIP350.Main
