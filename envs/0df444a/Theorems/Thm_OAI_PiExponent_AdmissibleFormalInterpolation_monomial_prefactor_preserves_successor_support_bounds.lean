-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_monomial_prefactor_preserves_successor_support_bounds
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.monomial_prefactor_preserves_successor_support_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T18:19:59.367037+00:00
-- url     : https://prove2.me/theorems/d15813bb-77c7-453e-815b-9d82d320756b
-- title:
--   Zeroth-coordinate monomial preserves successor support bounds
-- statement:
--   Multiplying a multivariate formal power series by a power of the zeroth variable preserves any stated bounds on its successor-coordinate support.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_FormalJetShear

open scoped BigOperators

theorem OAI.PiExponent.AdmissibleFormalInterpolation.monomial_prefactor_preserves_successor_support_bounds
    {m : ℕ} (n : ℕ) (b : Fin m → ℕ)
    (p : MvPowerSeries (Fin (m + 1)) ℂ)
    (e : Fin (m + 1) →₀ ℕ)
    (hp : ∀ d : Fin (m + 1) →₀ ℕ,
      MvPowerSeries.coeff d p ≠ 0 → ∀ i : Fin m, d i.succ ≤ b i)
    (hne : MvPowerSeries.coeff e (MvPowerSeries.X 0 ^ n * p) ≠ 0) :
    ∀ i : Fin m, e i.succ ≤ b i := by sorry
