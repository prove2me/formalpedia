-- Prove2me | Theorems.Thm_FourBlockIP350_Main_affine_subtraction
-- name    : FourBlockIP350.Main.affine_subtraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:47.73228+00:00
-- url     : https://prove2.me/theorems/488b3ba9-f282-418e-94b5-8a6db91c35d6
-- title:
--   Lemma 2.5 — Affine subtraction preserves midpoint convexity
-- statement:
--   For an everywhere real-valued midpoint-convex function $h:\mathbb Z^k\to\mathbb R$ and an affine function $A:\mathbb R^k\to\mathbb R$, the function
--   $$v\longmapsto h(v)-A(v)$$
--   is midpoint-convex. The affine evaluation uses the ordinary embedding of the integer lattice into the real space.
--
--   This preserves the precise integral-midpoint inequality while removing an affine function.
--
--   Differences from the source: none.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 5, Lemma 2.5

import Mathlib
import Definitions.Def_FourBlockIP350_Main_LatticeConvexity

namespace FourBlockIP350.Main

open scoped BigOperators

theorem affine_subtraction {k : ℕ} (hk : 0 < k) (h : ZVec k → ℝ)
    (hh : MidpointConvex h) (A : RVec k →ᵃ[ℝ] ℝ) :
    MidpointConvex (fun v => h v - A (realVec v)) := by sorry

end FourBlockIP350.Main
