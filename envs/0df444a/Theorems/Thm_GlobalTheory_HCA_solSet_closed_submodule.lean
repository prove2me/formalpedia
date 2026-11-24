-- Prove2me | Theorems.Thm_GlobalTheory_HCA_solSet_closed_submodule
-- name    : GlobalTheory.HCA.solSet_closed_submodule
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:32.198921+00:00
-- url     : https://prove2.me/theorems/9312f2ef-83cb-4c91-8f46-e79d8b799272
-- title:
--   HCA: sol Set closed submodule
-- statement:
--   The HCA construction uses the sol Set closed submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AestronglyMeasurableExtendByZeroOffSubset.lean#L106-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AestronglyMeasurableExtendByZeroOffSubset.lean#L106-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory.HCA.SolSub

theorem GlobalTheory.HCA.solSet_closed_submodule :
    ∀ (d : ℕ) (ι : Type) (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) →
      IsClosed (solSet P U) ∧ ∃ S : Submodule ℂ (U →ᵇ ℂ), (S : Set (U →ᵇ ℂ)) = solSet P U := by sorry
