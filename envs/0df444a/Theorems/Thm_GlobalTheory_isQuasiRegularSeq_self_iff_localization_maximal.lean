-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_self_iff_localization_maximal
-- name    : GlobalTheory.isQuasiRegularSeq_self_iff_localization_maximal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:28.899705+00:00
-- url     : https://prove2.me/theorems/7fbac251-4a68-42a8-bc43-8fa6a46fc2d2
-- title:
--   Global Theory: is Quasi Regular Seq self iff localization maximal
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq self iff localization maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L665-L672
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L665-L672

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

theorem GlobalTheory.isQuasiRegularSeq_self_iff_localization_maximal (f : ι → R) :
    IsQuasiRegularSeq R f ↔ ∀ (P : Ideal R) [P.IsMaximal], Ideal.span (Set.range f) ≤ P →
      IsQuasiRegularSeq (Localization.AtPrime P)
        fun i => algebraMap R (Localization.AtPrime P) (f i) := by sorry
