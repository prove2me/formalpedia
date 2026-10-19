-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_monomial_shear_factor_power_support_of_factor_support
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_factor_power_support_of_factor_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:19:12.619166+00:00
-- url     : https://prove2.me/theorems/382ade7f-f528-46ed-a849-50a58a9a899f
-- title:
--   Power support from single-factor support
-- statement:
--   If a multivariate power series has no support in any successor coordinate except one chosen coordinate, and its exponent in that coordinate is at most one, then its nth power has exponent at most n there and has no support in any other successor coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_factor_power_support_of_factor_support
    {m : ℕ} (i : Fin m) (n : ℕ)
    (f : MvPowerSeries (Fin (m + 1)) ℂ)
    (hf : ∀ e : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff e f ≠ 0 →
        e i.succ ≤ 1 ∧ ∀ j : Fin m, j ≠ i → e j.succ = 0)
    (d : Fin (m + 1) →₀ ℕ) :
    (MvPowerSeries.coeff d (f ^ n) ≠ 0 → d i.succ ≤ n) ∧
    (∀ j : Fin m, j ≠ i → d j.succ ≠ 0 →
      MvPowerSeries.coeff d (f ^ n) = 0) := by sorry
