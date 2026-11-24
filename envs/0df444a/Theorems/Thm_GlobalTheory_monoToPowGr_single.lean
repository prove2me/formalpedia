-- Prove2me | Theorems.Thm_GlobalTheory_monoToPowGr_single
-- name    : GlobalTheory.monoToPowGr_single
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:11:26.223957+00:00
-- url     : https://prove2.me/theorems/4c7ae3bb-8e2d-483b-9527-569a0fb51f8b
-- title:
--   Global Theory: mono To Pow Gr single
-- statement:
--   The Global Theory construction uses the mono To Pow Gr single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L277-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L277-L285

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

theorem GlobalTheory.monoToPowGr_single [DecidableEq ι] (f : ι → R) (a : ℕ) (α : MonoDeg ι a)
    (x : M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) :
    monoToPowGr M f a (Pi.single α x) =
      powGr.mulElem M (monoVal f α.1) (monoVal_mem_pow f α) x := by sorry
