-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_monomial_power_of_weight_bound
-- name    : OAI.PiExponent.LogarithmicJetIdeals.monomial_power_of_weight_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T19:37:27.094546+00:00
-- url     : https://prove2.me/theorems/62800a03-b4b5-4e42-9c14-976a1de234c1
-- title:
--   Weighted exponent bound gives monomial power membership
-- statement:
--   Under the positive scale hypotheses, a single exponent vector whose weighted degree meets the cutoff yields a monomial divisible by a product of n coordinate generators, so its monomial belongs to the nth power of their ideal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.monomial_power_of_weight_bound
    {m : ℕ} (e : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → ℝ) (R : ℝ)
    (hR : 0 < R) (hρ : ∀ i, 0 < ρ i) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * ρ i)
    (n : ℕ) (d : Fin (m + 1) →₀ ℕ)
    (hweight : (((n + m : ℕ) : ℝ) * R) ≤ ∑ i, ρ i * (d i : ℝ)) :
    MvPolynomial.monomial d (1 : ℂ) ∈
      (Ideal.span (Set.range (fun i : Fin (m + 1) =>
        MvPolynomial.X i ^ e i)) : Ideal (MvPolynomial (Fin (m + 1)) ℂ)) ^ n := by
  sorry
