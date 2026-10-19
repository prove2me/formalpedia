-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_formal_logarithmic_ideal_power_packet_vanishing
-- name    : OAI.PiExponent.FormalInterpolation.formal_logarithmic_ideal_power_packet_vanishing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T12:43:33.559654+00:00
-- url     : https://prove2.me/theorems/f7a41e08-adcb-4441-9753-d178e094483c
-- title:
--   Logarithmic center ideal powers annihilate strict formal packets
-- statement:
--   Under positive row weights, suppose each powered logarithmic coordinate has minimum weight at least R and each logarithmic tail starts at sufficient weight. Then every polynomial in the nth power of the product of logarithmic center ideals has zero formal coefficients at all row indices of weight strictly below nR. Prove this through the multiplicative weighted filtration of multivariate power series. No distinctness assumption on the centers is needed.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L20-L44; Approximation/AdmissibleMatrixInterpolation.lean#L117-L166 (WeightedPolynomials, packetMap and the cofinal radius).

import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.FormalInterpolation.formal_logarithmic_ideal_power_packet_vanishing
    {m : ℕ} (K : ℕ) (v0 theta : ℝ) (w : Fin m → ℝ)
    (r : Fin m → ℂ) (R : ℝ) (T : Fin m → ℕ) (e : Fin (m + 1) → ℕ)
    (hv0 : 0 < v0) (htheta : 0 < theta) (hw : ∀ i, 0 < w i)
    (hR : 0 < R)
    (hscale : ∀ i, R ≤ (e i : ℝ) * InterpolationMatrix.rowWeights v0 theta w i)
    (hT : ∀ i : Fin m,
      InterpolationMatrix.rowWeights v0 theta w i.succ ≤ (T i : ℝ) * v0)
    (n : ℕ) (P : MvPolynomial (Fin (m + 1)) ℂ)
    (hP : P ∈ (FormalInterpolation.logarithmicCentersIdeal
      (fun j : Fin K => fun i => (j.val : ℂ) * r i) T e) ^ n)
    (rho : InterpolationMatrix.Row K v0 theta w ((n : ℝ) * R)) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
      (FormalInterpolation.formalJet (fun i => (rho.1.val : ℂ) * r i) P) = 0 := by sorry
