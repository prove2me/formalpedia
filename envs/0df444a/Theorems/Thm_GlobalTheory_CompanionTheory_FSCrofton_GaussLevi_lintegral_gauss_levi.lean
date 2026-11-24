-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FSCrofton_GaussLevi_lintegral_gauss_levi
-- name    : GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_gauss_levi
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:42.744528+00:00
-- url     : https://prove2.me/theorems/9d9945f3-8609-4a4d-8c54-029809af4364
-- title:
--   Gauss Levi: lintegral gauss levi
-- statement:
--   The Gauss Levi construction uses the lintegral gauss levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetLeviIntegral.lean#L187-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianDetLeviIntegral.lean#L187-L239

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetSquareIntegralStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianDetLeviIntegral
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FSCrofton GlobalTheory.CompanionTheory.FSCrofton.GaussLevi
open Matrix
variable {β : Type} [Fintype β] [DecidableEq β]

theorem GlobalTheory.CompanionTheory.FSCrofton.GaussLevi.lintegral_gauss_levi : ∀ (d : ℕ) (β : Type) [Fintype β] [DecidableEq β] (f : β → ℂ)
    (F : Matrix β (Fin d) ℂ),
    ∫⁻ C : Fin d → β → ℂ, gW d β C *
        ENNReal.ofReal (Real.exp (-∑ k, ‖∑ j, C k j * f j‖ ^ 2) * ‖(Matrix.of C * F).det‖ ^ 2) =
      ENNReal.ofReal (Real.pi ^ (d * Fintype.card β) * (d.factorial : ℝ) * (fsLevi f F).det.re) := by sorry
