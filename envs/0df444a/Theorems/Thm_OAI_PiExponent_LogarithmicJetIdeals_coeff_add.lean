-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_add
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_add
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:33:41.779631+00:00
-- url     : https://prove2.me/theorems/40de30bd-6541-403a-86cb-81acddf6995e
-- title:
--   Coefficient extraction respects polynomial addition
-- statement:
--   For any two polynomials, coefficient extraction after evaluation at phi sends their sum to the sum of their evaluated coefficients. This supplies the additive step used to combine the original polynomial with the homogeneous correction.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_add
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (Q R : MvPolynomial (Fin n) Complex)
    (e : Fin n → Nat) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval phi (Q + R)) =
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval phi Q) +
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (MvPolynomial.aeval phi R) := by sorry
