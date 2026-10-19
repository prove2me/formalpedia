-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_linear_factor_coeff_degree_bound
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.linear_factor_coeff_degree_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:54:32.629987+00:00
-- url     : https://prove2.me/theorems/5ae45698-4e16-4924-9374-6a576fdf440b
-- title:
--   A constant-shifted coordinate has degree at most one
-- statement:
--   A nonzero coefficient of one variable plus a constant can occur only at total degree zero or one.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Basic

theorem OAI.PiExponent.AdmissibleFormalInterpolation.linear_factor_coeff_degree_bound
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (a : R) (m : σ →₀ ℕ)
    (hm : MvPowerSeries.coeff m
      (MvPowerSeries.X x + MvPowerSeries.C a) ≠ 0) :
    m.sum (fun _ k => k) ≤ 1 := by sorry
