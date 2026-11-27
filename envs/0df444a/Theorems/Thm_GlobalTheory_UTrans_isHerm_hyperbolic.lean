-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_isHerm_hyperbolic
-- name    : GlobalTheory.UTrans.isHerm_hyperbolic
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:59.564347+00:00
-- url     : https://prove2.me/theorems/49c7d93b-0772-59dc-adde-0ca99ad1fadc
-- title:
--   UTrans: is Herm hyperbolic
-- statement:
--   The UTrans construction uses the is Herm hyperbolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/IsHermHyperbolic.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/IsHermHyperbolic.lean#L27-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}

theorem GlobalTheory.UTrans.isHerm_hyperbolic : IsHerm (starRingEnd ℂ) !![0, 1; 1, 0] ∧
    ∃ z : Fin 2 → ℂ, z ≠ 0 ∧ hf (starRingEnd ℂ) !![0, 1; 1, 0] z z = 0 := by sorry
