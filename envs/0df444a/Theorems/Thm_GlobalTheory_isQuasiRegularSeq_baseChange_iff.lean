-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_baseChange_iff
-- name    : GlobalTheory.isQuasiRegularSeq_baseChange_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:10.073074+00:00
-- url     : https://prove2.me/theorems/bc987522-dba2-5fa5-8383-b92568f34e5f
-- title:
--   Global Theory: is Quasi Regular Seq base Change iff
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq base Change iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L594-L596
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L594-L596

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
variable (S : Type*) [CommRing S] [Algebra R S]

theorem GlobalTheory.isQuasiRegularSeq_baseChange_iff [Module.FaithfullyFlat R S] (f : ι → R) :
    (IsQuasiRegularSeq (S ⊗[R] M) fun i => algebraMap R S (f i)) ↔ IsQuasiRegularSeq M f := by sorry
