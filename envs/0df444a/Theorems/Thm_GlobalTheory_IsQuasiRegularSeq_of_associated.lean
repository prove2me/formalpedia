-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_associated
-- name    : GlobalTheory.IsQuasiRegularSeq.of_associated
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:18.765802+00:00
-- url     : https://prove2.me/theorems/996f904d-2e36-479f-afe4-94038186c8a1
-- title:
--   Is Quasi Regular Seq: of associated
-- statement:
--   The Is Quasi Regular Seq construction uses the of associated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L407-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L407-L411

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

theorem GlobalTheory.IsQuasiRegularSeq.of_associated {f g : ι → R} (h : IsQuasiRegularSeq M f) (hfg : ∀ i, Associated (f i) (g i)) :
    IsQuasiRegularSeq M g := by sorry
