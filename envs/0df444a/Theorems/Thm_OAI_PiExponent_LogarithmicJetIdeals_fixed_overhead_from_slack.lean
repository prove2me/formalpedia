-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_fixed_overhead_from_slack
-- name    : OAI.PiExponent.LogarithmicJetIdeals.fixed_overhead_from_slack
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T17:40:40.12598+00:00
-- url     : https://prove2.me/theorems/7aa9476e-dc41-4c2d-a95a-62faf2c2c980
-- title:
--   Absorbing fixed ideal-power overhead using scale slack
-- statement:
--   Given representatives at weight nR modulo the nth ideal power for all sufficiently large n, and a strict gap R < S, every fixed natural-number overhead B can be absorbed: for all sufficiently large k, there is a representative at weight kS modulo the (k+B)th ideal power. The strict inequality is essential to this argument; it handles B=0 as well, while the threshold also ensures k+B is in the range where the representative hypothesis applies.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.fixed_overhead_from_slack
    {nu : ℝ} (d : FixedData nu)
    (R S : ℝ) (T : Fin d.m → ℕ) (e : Fin (d.m + 1) → ℕ) (N : ℕ)
    (hR : 0 < R) (hRS : R < S)
    (hrep : ∀ n : ℕ, N ≤ n →
      ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
        ∃ Q : WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : ℝ) * R),
          P - Q.val ∈ (simultaneousJetIdeal d.K
            (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
            T e) ^ n) :
    ∀ B : ℕ, ∃ M : ℕ, ∀ k : ℕ, M ≤ k →
      ∀ P : MvPolynomial (Fin (d.m + 1)) ℂ,
        ∃ Q : WeightedPolynomial d.w0
            (MatrixArithmetic.logWeights (finiteDenominators d)) ((k : ℝ) * S),
          P - Q.val ∈ (simultaneousJetIdeal d.K
            (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
            T e) ^ (k + B) := by sorry
