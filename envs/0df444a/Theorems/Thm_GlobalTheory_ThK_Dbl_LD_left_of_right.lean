-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_left_of_right
-- name    : GlobalTheory.ThK.Dbl.LD.left_of_right
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:03:06.839165+00:00
-- url     : https://prove2.me/theorems/a896d71b-e84b-4784-9608-bbd113174a39
-- title:
--   LD: left of right
-- statement:
--   The LD construction uses the left of right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistB.lean#L53-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistB.lean#L53-L140

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem GlobalTheory.ThK.Dbl.LD.left_of_right (χ : G →* ℂ) (θ : G →* G) (cθ : Continuous θ) (iθ : ∀ x, θ (θ x) = x) {g : G} (hg : θ g = g⁻¹)
    (l : (G → ℂ) →ₗ[ℂ] ℂ) (hl : ∀ φ ∈ SB G, ∀ h, l (fun x => φ (x * h)) = χ h * l φ) {φ : G → ℂ} (hφ : φ ∈ SB G) :
    l (fun x => φ (g * x)) = χ g * l φ := by sorry
