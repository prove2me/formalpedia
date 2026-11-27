-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_iff_localization_maximal
-- name    : GlobalTheory.isQuasiRegularSeq_iff_localization_maximal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:09.939908+00:00
-- url     : https://prove2.me/theorems/35776236-9d85-5522-bdc1-d684a9c330a1
-- title:
--   Global Theory: is Quasi Regular Seq iff localization maximal
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq iff localization maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L656-L663
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L656-L663

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
variable {N : Type*} [AddCommGroup N] [Module R N]

theorem GlobalTheory.isQuasiRegularSeq_iff_localization_maximal (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ (P : Ideal R) [P.IsMaximal], Ideal.span (Set.range f) ≤ P →
      IsQuasiRegularSeq (LocalizedModule P.primeCompl M)
        fun i => algebraMap R (Localization.AtPrime P) (f i) := by sorry
