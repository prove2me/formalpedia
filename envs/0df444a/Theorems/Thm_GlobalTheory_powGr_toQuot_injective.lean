-- Prove2me | Theorems.Thm_GlobalTheory_powGr_toQuot_injective
-- name    : GlobalTheory.powGr.toQuot_injective
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:44.1768+00:00
-- url     : https://prove2.me/theorems/d51852db-fabf-478d-8ad6-e610c2589f1c
-- title:
--   pow Gr: to Quot injective
-- statement:
--   The pow Gr construction uses the to Quot injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L205-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L205-L209

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
variable {R : Type*} [CommRing R]
open GlobalTheory.powGr
variable (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] (a : ℕ)

theorem GlobalTheory.powGr.toQuot_injective : Function.Injective (toQuot I M a) := by sorry
