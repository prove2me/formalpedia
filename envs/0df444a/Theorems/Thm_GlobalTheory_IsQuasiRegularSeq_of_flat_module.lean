-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_flat_module
-- name    : GlobalTheory.IsQuasiRegularSeq.of_flat_module
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:21:34.619582+00:00
-- url     : https://prove2.me/theorems/ce7a889d-a028-40c2-8769-fdedd2470b95
-- title:
--   Is Quasi Regular Seq: of flat module
-- statement:
--   The Is Quasi Regular Seq construction uses the of flat module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L580-L582
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L580-L582

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

theorem GlobalTheory.IsQuasiRegularSeq.of_flat_module {f : ι → R} (h : IsQuasiRegularSeq R f) (N : Type*)
    [AddCommGroup N] [Module R N] [Module.Flat R N] : IsQuasiRegularSeq N f := by sorry
