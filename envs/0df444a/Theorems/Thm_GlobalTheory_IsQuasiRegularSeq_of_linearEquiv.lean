-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_linearEquiv
-- name    : GlobalTheory.IsQuasiRegularSeq.of_linearEquiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:07.908831+00:00
-- url     : https://prove2.me/theorems/5cca4de9-23d0-4457-a65c-bf68111ae3ef
-- title:
--   Is Quasi Regular Seq: of linear Equiv
-- statement:
--   The Is Quasi Regular Seq construction uses the of linear Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L413-L419
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L413-L419

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

theorem GlobalTheory.IsQuasiRegularSeq.of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N] {f : ι → R}
    (h : IsQuasiRegularSeq M f) (e : M ≃ₗ[R] N) : IsQuasiRegularSeq N f := by sorry
