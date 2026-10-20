-- Prove2me | Theorems.Thm_Gerver_sofa_cap_niche
-- name    : Gerver.sofa_cap_niche
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T20:10:18.648265+00:00
-- url     : https://prove2.me/theorems/201ccc6e-c23b-4c68-b737-956e7172dafa
-- title:
--   A moving monotone sofa is its cap minus its niche
-- statement:
--   Let x be a supporting rotation path of angle ω ∈ (0, π/2] whose monotone sofa sofaOfPath x ω is a moving sofa. Then the monotone sofa equals its cap minus its niche — the cap being the part of the parallelogram P_ω cut out by the outer quarter-planes, the niche the part of the fan swept by the inner quarter-planes — and the niche lies inside the cap. Together with the area-functional milestone this identifies the moving sofa with its cap, the sofa problem becoming the maximization of |K| - |N(K)| over caps K.
-- source:
--   Baek (2024), Optimality of Gerver's Sofa, arXiv:2411.19826, Theorem 2.4.2 and Theorem 2.5.9 (Step 1-(a) of the proof outline)

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone
import Definitions.Def_Gerver_sofa

namespace Gerver

/-- Step 1a (Theorem 2.4.2 and Theorem 2.5.9): a moving monotone sofa with a
supporting rotation path is its cap minus its niche, and the niche lies
inside the cap. -/
theorem sofa_cap_niche (x : ℝ → ℝ × ℝ) {ω : ℝ} (hω : 0 < ω) (hω' : ω ≤ Real.pi / 2)
    (hsup : IsSupportingPathOf x ω) (hm : IsMovingSofa (sofaOfPath x ω)) :
    sofaOfPath x ω = capOf x ω \ nicheOf x ω ∧ nicheOf x ω ⊆ capOf x ω := by
  sorry

end Gerver
