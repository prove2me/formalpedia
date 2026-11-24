-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_flat
-- name    : GlobalTheory.IsQuasiRegularSeq.of_flat
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:27:04.783118+00:00
-- url     : https://prove2.me/theorems/fb6cc419-dd5c-45d4-9279-ec57c837a716
-- title:
--   Is Quasi Regular Seq: of flat
-- statement:
--   The Is Quasi Regular Seq construction uses the of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L590-L592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L590-L592

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

theorem GlobalTheory.IsQuasiRegularSeq.of_flat [Module.Flat R S] {f : ι → R} (h : IsQuasiRegularSeq R f) :
    IsQuasiRegularSeq S fun i => algebraMap R S (f i) := by sorry
