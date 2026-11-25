-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_baseChange
-- name    : GlobalTheory.IsQuasiRegularSeq.baseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:22.116904+00:00
-- url     : https://prove2.me/theorems/d6999a56-2365-47e7-9a33-5f658ba714a7
-- title:
--   Is Quasi Regular Seq: base Change
-- statement:
--   The Is Quasi Regular Seq construction uses the base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L586-L588
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L586-L588

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
variable (S : Type*) [CommRing S] [Algebra R S]

theorem GlobalTheory.IsQuasiRegularSeq.baseChange [Module.Flat R S] {f : ι → R} (h : IsQuasiRegularSeq M f) :
    IsQuasiRegularSeq (S ⊗[R] M) fun i => algebraMap R S (f i) := by sorry
