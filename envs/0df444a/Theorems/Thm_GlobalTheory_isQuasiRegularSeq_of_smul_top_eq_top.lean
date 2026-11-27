-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_of_smul_top_eq_top
-- name    : GlobalTheory.isQuasiRegularSeq_of_smul_top_eq_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:14.197921+00:00
-- url     : https://prove2.me/theorems/beba3e1a-d425-5536-af6e-705a7f263182
-- title:
--   Global Theory: is Quasi Regular Seq of smul top eq top
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq of smul top eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L435-L437
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L435-L437

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

theorem GlobalTheory.isQuasiRegularSeq_of_smul_top_eq_top {f : ι → R}
    (h : (Ideal.span (Set.range f) • ⊤ : Submodule R M) = ⊤) : IsQuasiRegularSeq M f := by sorry
