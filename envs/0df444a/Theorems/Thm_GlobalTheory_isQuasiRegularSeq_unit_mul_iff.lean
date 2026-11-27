-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_unit_mul_iff
-- name    : GlobalTheory.isQuasiRegularSeq_unit_mul_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:19.817803+00:00
-- url     : https://prove2.me/theorems/884534e6-ddd7-50ea-9cdb-ab92e1b71393
-- title:
--   Global Theory: is Quasi Regular Seq unit mul iff
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq unit mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L427-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L427-L429

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

theorem GlobalTheory.isQuasiRegularSeq_unit_mul_iff (f : ι → R) {u : ι → R} (hu : ∀ i, IsUnit (u i)) :
    (IsQuasiRegularSeq M fun i => u i * f i) ↔ IsQuasiRegularSeq M f := by sorry
