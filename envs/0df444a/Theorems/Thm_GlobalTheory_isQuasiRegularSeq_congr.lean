-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_congr
-- name    : GlobalTheory.isQuasiRegularSeq_congr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:47:17.047516+00:00
-- url     : https://prove2.me/theorems/2df0f394-d4b6-5b4d-b019-97e13a708324
-- title:
--   Global Theory: is Quasi Regular Seq congr
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L431-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L431-L433

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

theorem GlobalTheory.isQuasiRegularSeq_congr {N : Type*} [AddCommGroup N] [Module R N] (f : ι → R)
    (e : M ≃ₗ[R] N) : IsQuasiRegularSeq M f ↔ IsQuasiRegularSeq N f := by sorry
