-- Prove2me | Theorems.Thm_MasulloRH_subpole_blowup_excludes_meromorphic_quotient
-- name    : MasulloRH.subpole_blowup_excludes_meromorphic_quotient
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T10:47:09.874253+00:00
-- url     : https://prove2.me/theorems/cc141d3b-0b3c-498e-a4f1-b5458a09e6f6
-- title:
--   Punctured blow-up slower than a simple pole prevents a meromorphic trace germ
-- statement:
--   Along any nontrivial approach to a point in the punctured complex plane, if the norm tends to infinity while multiplication by the distance makes it tend to zero, the germ is not meromorphic there. The approach can be the left real radius, without restricting the function value at the endpoint.
-- source:
--   Masullo trace comparison: meromorphy test for logarithmic Fredholm determinant derivatives in mission discussion 108c42e3-c0c1-4f5a-9ec0-eede0f611455.

import Mathlib
open Filter Topology

theorem MasulloRH.subpole_blowup_excludes_meromorphic_quotient (f : ℂ → ℂ) (a : ℂ) (l : Filter ℂ) [l.NeBot]
    (hl : l ≤ 𝓝[≠] a)
    (hinf : Tendsto (fun z => ‖f z‖) l atTop)
    (hsub : Tendsto (fun z => ‖(z-a)*f z‖) l (𝓝 0)) :
    ¬ MeromorphicAt f a := by sorry
