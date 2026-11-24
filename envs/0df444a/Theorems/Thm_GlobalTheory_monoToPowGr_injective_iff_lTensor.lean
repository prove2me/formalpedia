-- Prove2me | Theorems.Thm_GlobalTheory_monoToPowGr_injective_iff_lTensor
-- name    : GlobalTheory.monoToPowGr_injective_iff_lTensor
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:11:01.430911+00:00
-- url     : https://prove2.me/theorems/64aa522c-6f7e-4e83-823c-083e541a8c09
-- title:
--   Global Theory: mono To Pow Gr injective iff l Tensor
-- statement:
--   The Global Theory construction uses the mono To Pow Gr injective iff l Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L529-L555
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L529-L555

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
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]

theorem GlobalTheory.monoToPowGr_injective_iff_lTensor (f : ι → R) (a : ℕ) :
    Function.Injective (monoToPowGr M f a) ↔
      Function.Injective ((monoToQuotPow f a).lTensor M) := by sorry
