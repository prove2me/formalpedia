-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_complex
-- name    : GlobalTheory.EigenSplit.isSplitting_complex
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:33.431221+00:00
-- url     : https://prove2.me/theorems/0f48b386-1970-4327-9832-2f9abadedfdf
-- title:
--   Eigen Split: is Splitting complex
-- statement:
--   The Eigen Split construction uses the is Splitting complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L795-L800
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L795-L800

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

theorem GlobalTheory.EigenSplit.isSplitting_complex (E : Type*) [Field E] [NumberField E] :
    IsSplitting fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E) := by sorry
