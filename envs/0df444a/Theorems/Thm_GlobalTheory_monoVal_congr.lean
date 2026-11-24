-- Prove2me | Theorems.Thm_GlobalTheory_monoVal_congr
-- name    : GlobalTheory.monoVal_congr
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:43.278334+00:00
-- url     : https://prove2.me/theorems/f87289c2-a82f-4be5-a851-4acbddf5fc9c
-- title:
--   Global Theory: mono Val congr
-- statement:
--   The Global Theory construction uses the mono Val congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L73-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L73-L75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} {ι : Type*}

theorem GlobalTheory.monoVal_congr [CommMonoid R] {κ : Type*} (e : ι ≃ κ) (f : κ → R) (a : ℕ)
    (α : MonoDeg ι a) : monoVal f (MonoDeg.congr e a α).1 = monoVal (f ∘ e) α.1 := by sorry
