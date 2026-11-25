-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_iff_finsuppAntidiag
-- name    : GlobalTheory.isQuasiRegularSeq_iff_finsuppAntidiag
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:17.392337+00:00
-- url     : https://prove2.me/theorems/dfc84cb9-fa7f-52e7-903d-26a9ba431885
-- title:
--   Global Theory: is Quasi Regular Seq iff finsupp Antidiag
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq iff finsupp Antidiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L319-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L319-L334

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
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {M}

theorem GlobalTheory.isQuasiRegularSeq_iff_finsuppAntidiag {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → R) :
    IsQuasiRegularSeq M f ↔ ∀ (a : ℕ) (c : (ι →₀ ℕ) → M),
      ∑ α ∈ Finset.finsuppAntidiag Finset.univ a, monoVal f α • c α ∈
        (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M) →
      ∀ α, α.degree = a → c α ∈ (Ideal.span (Set.range f) • ⊤ : Submodule R M) := by sorry
