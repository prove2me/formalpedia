-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_isLocalizedModule
-- name    : GlobalTheory.IsQuasiRegularSeq.of_isLocalizedModule
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:34:03.780333+00:00
-- url     : https://prove2.me/theorems/4a1ab9cb-2af7-4e71-885b-9ba416c9a7e5
-- title:
--   Is Quasi Regular Seq: of is Localized Module
-- statement:
--   The Is Quasi Regular Seq construction uses the of is Localized Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L605-L609
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L605-L609

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

theorem GlobalTheory.IsQuasiRegularSeq.of_isLocalizedModule [Module S N] [IsScalarTower R S N]
    (T : Submonoid R) [IsLocalization T S] (g : M →ₗ[R] N) [IsLocalizedModule T g] {f : ι → R}
    (h : IsQuasiRegularSeq M f) : IsQuasiRegularSeq N fun i => algebraMap R S (f i) := by sorry
