-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coefficients_interpolating_polynomials
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_interpolating_polynomials
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T09:05:49.894115+00:00
-- url     : https://prove2.me/theorems/2aa52d7a-ba59-4620-a114-62ffaf26a89e
-- title:
--   Polynomial interpolation for distinct formal-jet coefficient functionals
-- statement:
--   There are polynomials that interpolate the finite family of formal-jet coefficient functionals: the coefficient indexed by x evaluates to one on Q_x and zero on every Q_y with y ≠ x.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Mathlib.LinearAlgebra.LinearIndependent.Basic

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_interpolating_polynomials
    {m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : ι → Fin m → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (hindex : Function.Injective (fun x => (c x, exponent x))) :
    ∃ Q : ι → MvPolynomial (Fin (m + 1)) ℂ,
      ∀ x y, MvPowerSeries.coeff (exponent x) (formalJet (c x) (Q y)) =
        if x = y then 1 else 0 := by sorry
