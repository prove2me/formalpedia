-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_iff_lTensor
-- name    : GlobalTheory.isQuasiRegularSeq_iff_lTensor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:34.152152+00:00
-- url     : https://prove2.me/theorems/29482de8-311a-453a-8e05-846c8f9905ef
-- title:
--   Global Theory: is Quasi Regular Seq iff l Tensor
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq iff l Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L557-L560
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L557-L560

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

theorem GlobalTheory.isQuasiRegularSeq_iff_lTensor (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ a, Function.Injective ((monoToQuotPow f a).lTensor M) := by sorry
