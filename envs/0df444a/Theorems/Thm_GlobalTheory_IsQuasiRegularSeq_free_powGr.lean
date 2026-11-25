-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_free_powGr
-- name    : GlobalTheory.IsQuasiRegularSeq.free_powGr
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:02.401612+00:00
-- url     : https://prove2.me/theorems/91a4ef15-646c-455b-9855-3fbfba6e3700
-- title:
--   Is Quasi Regular Seq: free pow Gr
-- statement:
--   The Is Quasi Regular Seq construction uses the free pow Gr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L491-L496
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L491-L496

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

theorem GlobalTheory.IsQuasiRegularSeq.free_powGr {M : Type*} [AddCommGroup M] [Module R M] {f : ι → R}
    (h : IsQuasiRegularSeq M f) (a : ℕ)
    [Module.Free (R ⧸ Ideal.span (Set.range f))
      (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M))] :
    Module.Free (R ⧸ Ideal.span (Set.range f)) (powGr (Ideal.span (Set.range f)) M a) := by sorry
