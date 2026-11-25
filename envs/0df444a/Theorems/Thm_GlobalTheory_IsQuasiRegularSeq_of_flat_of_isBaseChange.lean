-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_flat_of_isBaseChange
-- name    : GlobalTheory.IsQuasiRegularSeq.of_flat_of_isBaseChange
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:21:56.605496+00:00
-- url     : https://prove2.me/theorems/4b3a5d60-9f70-410c-a446-e188b37f0c55
-- title:
--   Is Quasi Regular Seq: of flat of is Base Change
-- statement:
--   The Is Quasi Regular Seq construction uses the of flat of is Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L600-L603
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L600-L603

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
variable {N : Type*} [AddCommGroup N] [Module R N]

theorem GlobalTheory.IsQuasiRegularSeq.of_flat_of_isBaseChange [Module S N] [IsScalarTower R S N]
    [Module.Flat R S] {g : M →ₗ[R] N} (hg : IsBaseChange S g) {f : ι → R}
    (h : IsQuasiRegularSeq M f) : IsQuasiRegularSeq N fun i => algebraMap R S (f i) := by sorry
