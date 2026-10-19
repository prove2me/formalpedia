-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_monomial_shear_factor_power_support
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_factor_power_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:13:00.435983+00:00
-- url     : https://prove2.me/theorems/1e8d03c7-310d-491b-85c5-7ea55357fbd4
-- title:
--   Support bound for powers of one shifted coordinate
-- statement:
--   For a shifted coordinate raised to a natural power, any nonzero coefficient has matching successor exponent at most the power, and vanishes whenever it uses a different successor coordinate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.monomial_shear_factor_power_support
    {m : ℕ} (i : Fin m) (n : ℕ)
    (g : Fin m → MvPowerSeries (Fin (m + 1)) ℂ)
    (hg : ∀ k : Fin m, ∀ d : Fin (m + 1) →₀ ℕ, ∀ j : Fin m,
      d j.succ ≠ 0 → MvPowerSeries.coeff d (g k) = 0)
    (d : Fin (m + 1) →₀ ℕ) :
    (MvPowerSeries.coeff d ((MvPowerSeries.X i.succ + g i) ^ n) ≠ 0 →
      d i.succ ≤ n) ∧
    (∀ j : Fin m, j ≠ i → d j.succ ≠ 0 →
      MvPowerSeries.coeff d ((MvPowerSeries.X i.succ + g i) ^ n) = 0) := by sorry
