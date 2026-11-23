-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_tensor
-- name    : GlobalTheory.IsQuasiRegularSeq.tensor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:55.352034+00:00
-- url     : https://prove2.me/theorems/1c945b9b-fac3-47b1-8bce-1d21cea0a0d4
-- title:
--   Is Quasi Regular Seq: tensor
-- statement:
--   The Is Quasi Regular Seq construction uses the tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L569-L573
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L569-L573

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

theorem GlobalTheory.IsQuasiRegularSeq.tensor {f : ι → R} (h : IsQuasiRegularSeq M f) (N : Type*)
    [AddCommGroup N] [Module R N] [Module.Flat R N] : IsQuasiRegularSeq (N ⊗[R] M) f := by sorry
