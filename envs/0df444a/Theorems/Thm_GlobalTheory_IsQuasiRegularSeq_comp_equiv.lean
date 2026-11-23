-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_comp_equiv
-- name    : GlobalTheory.IsQuasiRegularSeq.comp_equiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:45.202749+00:00
-- url     : https://prove2.me/theorems/d9636742-c56c-4789-ad25-fc79ee4688a7
-- title:
--   Is Quasi Regular Seq: comp equiv
-- statement:
--   The Is Quasi Regular Seq construction uses the comp equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L386-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L386-L393

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

theorem GlobalTheory.IsQuasiRegularSeq.comp_equiv {κ : Type*} [Finite κ] {f : ι → R} (h : IsQuasiRegularSeq M f) (e : κ ≃ ι) :
    IsQuasiRegularSeq M (f ∘ e) := by sorry
