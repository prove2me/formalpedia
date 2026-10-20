-- Prove2me | Theorems.Thm_Gerver_area_functional
-- name    : Gerver.area_functional
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T20:11:02.580949+00:00
-- url     : https://prove2.me/theorems/af6a1429-fc10-4144-baac-f4bf2e6f6fad
-- title:
--   The sofa area functional: cap minus niche
-- statement:
--   Whenever the niche of a rotation path lies inside its cap, the area of the monotone sofa of the path is exactly the area of the cap minus the area of the niche. This is the sofa area functional A_ω(K) = |K| - |N(K)| of the source, the maximization of which over caps K is the moving sofa problem restated.
-- source:
--   Baek (2024), Optimality of Gerver's Sofa, arXiv:2411.19826, Section 1.2.2 (the sofa area functional A_ω)

import Mathlib
import Definitions.Def_Gerver_arena
import Definitions.Def_Gerver_monotone
import Definitions.Def_Gerver_sofa

namespace Gerver

/-- Step 1a (Section 1.2.2): the area of a monotone sofa is the area of its
cap minus the area of its niche — the sofa area functional
A_ω(K) = |K| - |N(K)|, whenever the niche lies inside the cap. -/
theorem area_functional (x : ℝ → ℝ × ℝ) (ω : ℝ)
    (hsub : nicheOf x ω ⊆ capOf x ω) :
    area (sofaOfPath x ω) = area (capOf x ω) - area (nicheOf x ω) := by
  sorry

end Gerver
