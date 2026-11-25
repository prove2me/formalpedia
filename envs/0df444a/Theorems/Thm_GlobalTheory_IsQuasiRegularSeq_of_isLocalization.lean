-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_isLocalization
-- name    : GlobalTheory.IsQuasiRegularSeq.of_isLocalization
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:33.613939+00:00
-- url     : https://prove2.me/theorems/6dd5eb5e-5f48-494b-a595-a51dc1391e56
-- title:
--   Is Quasi Regular Seq: of is Localization
-- statement:
--   The Is Quasi Regular Seq construction uses the of is Localization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L617-L619
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L617-L619

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

theorem GlobalTheory.IsQuasiRegularSeq.of_isLocalization (T : Submonoid R) [IsLocalization T S] {f : ι → R}
    (h : IsQuasiRegularSeq R f) : IsQuasiRegularSeq S fun i => algebraMap R S (f i) := by sorry
