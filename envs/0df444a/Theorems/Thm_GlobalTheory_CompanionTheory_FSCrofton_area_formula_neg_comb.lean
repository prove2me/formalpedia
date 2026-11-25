-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_area_formula_neg_comb
-- name    : GlobalTheory.CompanionTheory.FSCrofton.area_formula_neg_comb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:51.803673+00:00
-- url     : https://prove2.me/theorems/4f1d888b-0e51-4d21-b3a6-a1e8d9f7e7de
-- title:
--   FSCrofton: area formula neg comb
-- statement:
--   The FSCrofton construction uses the area formula neg comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChangeVariablesZeroCount.lean#L26-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ChangeVariablesZeroCount.lean#L26-L99

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ChangeVariablesZeroCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton

theorem GlobalTheory.CompanionTheory.FSCrofton.area_formula_neg_comb (d : ℕ) (β : Type) [Fintype β] (U A : Set (V d)) (f : β → V d → ℂ)
    (C : Fin d → β → ℂ) (h : (Fin d → ℂ) → ℝ≥0∞) (hU : IsOpen U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (hAU : A ⊆ U) (hA : MeasurableSet A)
    (hh : Measurable h) :
    ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞) =
      ∫⁻ z in A, h (fun k => -∑ j, C k j * f j z) *
        ENNReal.ofReal (‖(Matrix.of C * (Matrix.of fun j a =>
          fderiv ℂ (f j) z (EuclideanSpace.single a 1) : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by sorry
