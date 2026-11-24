-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_unit_mul
-- name    : GlobalTheory.IsQuasiRegularSeq.unit_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:11.224378+00:00
-- url     : https://prove2.me/theorems/7180f6e3-790f-44d4-9759-fa268d0a2b2e
-- title:
--   Is Quasi Regular Seq: unit mul
-- statement:
--   The Is Quasi Regular Seq construction uses the unit mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L395-L405
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L395-L405

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
open GlobalTheory.IsQuasiRegularSeq

theorem GlobalTheory.IsQuasiRegularSeq.unit_mul {f : ι → R} (h : IsQuasiRegularSeq M f) {u : ι → R} (hu : ∀ i, IsUnit (u i)) :
    IsQuasiRegularSeq M fun i => u i * f i := by sorry
