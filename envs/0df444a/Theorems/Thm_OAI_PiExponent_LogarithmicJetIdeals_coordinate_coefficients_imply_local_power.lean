-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coordinate_coefficients_imply_local_power
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coordinate_coefficients_imply_local_power
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T13:47:45.987885+00:00
-- url     : https://prove2.me/theorems/287deaf1-6658-4379-afb1-c4afba12df40
-- title:
--   Low coordinate coefficients imply membership in a local jet ideal power
-- statement:
--   If the polynomial in truncated logarithmic coordinates has no coefficients of weighted degree strictly below $(n+m)R$, with positive weights and $e_iρ_i=R$, then the original polynomial belongs to the $n$th power of its local jet ideal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coordinate_coefficients_imply_local_power
    {m : ℕ} (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m + 1) → ℕ) (ρ : Fin (m + 1) → ℝ) (R : ℝ)
    (hR : 0 < R) (hρ : ∀ i, 0 < ρ i) (he : ∀ i, 0 < e i)
    (hscale : ∀ i, R = (e i : ℝ) * ρ i)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hcoord : ∀ a : Fin (m + 1) → ℕ,
      (∑ i, ρ i * (a i : ℝ)) < (((n + m : ℕ) : ℝ) * R) →
      MvPolynomial.coeff (InterpolationMatrix.exponentVector a)
        (localCoordinatePolynomial c T P) = 0) :
    P ∈ (localJetIdeal c T e) ^ n := by sorry
