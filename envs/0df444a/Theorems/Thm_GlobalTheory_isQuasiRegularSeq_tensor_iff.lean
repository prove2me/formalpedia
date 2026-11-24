-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_tensor_iff
-- name    : GlobalTheory.isQuasiRegularSeq_tensor_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:00:21.117446+00:00
-- url     : https://prove2.me/theorems/306dbc48-398c-4e34-a662-72c7cdc57b93
-- title:
--   Global Theory: is Quasi Regular Seq tensor iff
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq tensor iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L575-L578
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L575-L578

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

theorem GlobalTheory.isQuasiRegularSeq_tensor_iff (f : ι → R) (N : Type*) [AddCommGroup N] [Module R N]
    [Module.FaithfullyFlat R N] : IsQuasiRegularSeq (N ⊗[R] M) f ↔ IsQuasiRegularSeq M f := by sorry
