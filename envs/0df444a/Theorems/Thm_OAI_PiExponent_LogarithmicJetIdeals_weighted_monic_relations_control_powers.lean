-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_monic_relations_control_powers
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_monic_relations_control_powers
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T21:38:24.136971+00:00
-- url     : https://prove2.me/theorems/214d09d5-b55d-4855-b411-8d2fd707a525
-- title:
--   Weighted monic coordinate relations control all ideal powers
-- statement:
--   For any ideal and positive coordinate weights, monic coordinate relations in one positive ideal power yield representatives modulo every ideal power with linear weighted-degree growth and an explicit constant overhead. Weighted division leaves only exponents whose sum of coordinatewise integer quotients is small.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_monic_relations_control_powers
    {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ)
    (hw : ∀ i, 0 < InterpolationMatrix.columnWeights w0 w i)
    (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (k : ℕ) (hk : 0 < k)
    (b : Fin (m + 1) → ℕ) (hb : ∀ i, 0 < b i)
    (F : Fin (m + 1) → MvPolynomial (Fin (m + 1)) ℂ)
    (hF : ∀ i, F i ∈ I ^ k)
    (hbelow : ∀ i, ∀ u ∈ (MvPolynomial.X i ^ b i - F i).support,
      (∑ j, InterpolationMatrix.columnWeights w0 w j * (u j : ℝ)) <
        InterpolationMatrix.columnWeights w0 w i * (b i : ℝ))
    (a : ℝ) (ha : 0 < a)
    (hsize : ∀ i, InterpolationMatrix.columnWeights w0 w i * (b i : ℝ) ≤
      (k : ℝ) * a) :
    ∀ n : ℕ, ∀ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∃ Q : WeightedPolynomial w0 w
          ((n : ℝ) * a +
            ∑ i, InterpolationMatrix.columnWeights w0 w i * ((b i - 1 : ℕ) : ℝ)),
        P - Q.val ∈ I ^ n := by sorry
