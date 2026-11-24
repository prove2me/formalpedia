-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_self_iff
-- name    : GlobalTheory.isQuasiRegularSeq_self_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:59:54.280918+00:00
-- url     : https://prove2.me/theorems/8b63b6a8-4d3d-4564-9a2a-cf1095b32bb8
-- title:
--   Global Theory: is Quasi Regular Seq self iff
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq self iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L336-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L336-L373

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

theorem GlobalTheory.isQuasiRegularSeq_self_iff (f : ι → R) :
    IsQuasiRegularSeq R f ↔ ∀ (a : ℕ) (p : MvPolynomial ι R), p.IsHomogeneous a →
      MvPolynomial.eval f p ∈ Ideal.span (Set.range f) ^ (a + 1) →
        ∀ α, p.coeff α ∈ Ideal.span (Set.range f) := by sorry
