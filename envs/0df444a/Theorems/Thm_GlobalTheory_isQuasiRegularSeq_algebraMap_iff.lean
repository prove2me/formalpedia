-- Prove2me | Theorems.Thm_GlobalTheory_isQuasiRegularSeq_algebraMap_iff
-- name    : GlobalTheory.isQuasiRegularSeq_algebraMap_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:03.240538+00:00
-- url     : https://prove2.me/theorems/f3c5eab3-0805-4c31-b461-50262dbd5f07
-- title:
--   Global Theory: is Quasi Regular Seq algebra Map iff
-- statement:
--   The Global Theory construction uses the is Quasi Regular Seq algebra Map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L439-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L439-L450

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

theorem GlobalTheory.isQuasiRegularSeq_algebraMap_iff (S : Type*) [CommRing S] [Algebra R S] [Module S M]
    [IsScalarTower R S M] (f : ι → R) :
    IsQuasiRegularSeq M (fun i => algebraMap R S (f i)) ↔ IsQuasiRegularSeq M f := by sorry
