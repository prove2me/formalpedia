-- Prove2me | Theorems.Thm_GlobalTheory_HaarScaleMatrix_integral_comp_addEquiv_matrix
-- name    : GlobalTheory.HaarScaleMatrix.integral_comp_addEquiv_matrix
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:32.743061+00:00
-- url     : https://prove2.me/theorems/44225b00-c3e5-4575-b002-d67be4cee1dd
-- title:
--   Haar Scale Matrix: integral comp add Equiv matrix
-- statement:
--   The Haar Scale Matrix construction uses the integral comp add Equiv matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarMeasureAdditiveAutomorphismScale.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HaarMeasureAdditiveAutomorphismScale.lean#L31-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FullRk
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarMeasureAdditiveAutomorphismScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory
open GlobalTheory GlobalTheory.HaarScaleMatrix

theorem GlobalTheory.HaarScaleMatrix.integral_comp_addEquiv_matrix :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (e d : ℕ)
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure]
    (L : Matrix (Fin e) (Fin d) k ≃+ Matrix (Fin e) (Fin d) k), Continuous L → Continuous L.symm →
    ∃ c : ℝ, 0 < c ∧ ∀ f : Matrix (Fin e) (Fin d) k → ℂ, ∫ x, f (L x) ∂μ = (c : ℂ) * ∫ x, f x ∂μ := by sorry
