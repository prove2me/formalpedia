-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_weightedShear_comp_of_weightedOrder
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_comp_of_weightedOrder
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:32:50.805193+00:00
-- url     : https://prove2.me/theorems/536c5c84-3e6a-4524-b21b-86a3612cf680
-- title:
--   Addition law for weighted shears with a weight-preserving outer substitution
-- statement:
--   For positive coordinate weights, suppose E_i vanishes below degree N_i and u_i ≤ N_i v0. For any family D of power series and any real strict cutoff H, applying the finite shear by D and then by E equals the finite shear by D+E. Only the outer substitution needs the weighted-order condition, since it prevents omitted intermediate coefficients from returning below the cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.weightedShear_comp_of_weightedOrder
    {m : ℕ} (v0 : ℝ) (u : Fin m → ℝ) (H : ℝ)
    (N : Fin m → ℕ) (D E : Fin m → PowerSeries ℂ)
    (hv0 : 0 < v0) (hu : ∀ i, 0 < u i)
    (hN : ∀ i, u i ≤ (N i : ℝ) * v0)
    (hE : ∀ i n, n < N i → PowerSeries.coeff n (E i) = 0) :
    (weightedShear (m := m) v0 u H E) ∘ₗ
        (weightedShear (m := m) v0 u H D) =
      weightedShear (m := m) v0 u H (fun i : Fin m => D i + E i) := by sorry
