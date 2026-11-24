-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_comp_equiv_iff
-- name    : GlobalTheory.isQuasiRegularSeq_comp_equiv_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:00:16.937035+00:00
-- url     : https://prove2.me/theorems/77a77d3b-5c0c-4f12-a70d-4f332c27a5f6
-- title:
--   Global Theory: is Quasi Regular Seq comp equiv iff
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq comp equiv iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L423-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L423-L425

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

theorem GlobalTheory.isQuasiRegularSeq_comp_equiv_iff {κ : Type*} [Finite κ] (f : ι → R) (e : κ ≃ ι) :
    IsQuasiRegularSeq M (f ∘ e) ↔ IsQuasiRegularSeq M f := by sorry
