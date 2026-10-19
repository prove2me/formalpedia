-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_subst_coeff_support
-- name    : OAI.PiExponent.LogarithmicJetIdeals.subst_coeff_support
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T22:19:22.552617+00:00
-- url     : https://prove2.me/theorems/f2ceb9d3-663c-45e6-8eee-3a87a5275e24
-- title:
--   Extract a nonzero term from a substitution coefficient
-- statement:
--   For an admissible multivariate power series substitution, every nonzero output coefficient has a contributing input exponent whose input coefficient and substituted monomial-product coefficient are both nonzero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Substitution
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.subst_coeff_support
    {m : ℕ} (sigma : Fin (m + 1) → MvPowerSeries (Fin (m + 1)) ℂ)
    (hsigma : MvPowerSeries.HasSubst sigma)
    (F : MvPowerSeries (Fin (m + 1)) ℂ)
    (e : Fin (m + 1) →₀ ℕ)
    (h : MvPowerSeries.coeff e (MvPowerSeries.subst sigma F) ≠ 0) :
    ∃ d : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff d F ≠ 0 ∧
      MvPowerSeries.coeff e (d.prod fun i n => sigma i ^ n) ≠ 0 := by sorry
