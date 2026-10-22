-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_sum_coeff_of_terms
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_sum_coeff_of_terms
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:41:39.113552+00:00
-- url     : https://prove2.me/theorems/99385e96-1a26-4891-8a1c-3d8785b18029
-- title:
--   Coefficient extraction from a finite sum of indexed series
-- statement:
--   For an indexed family of multivariate power series whose queried coefficient is zero except for the matching index, the coefficient of the finite sum over exactly the degree-m indices is the matching value when the queried degree is m, and zero for queried degrees at most m otherwise.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_sum_coeff_of_terms
    {n : Nat}
    (f : (Fin n → Nat) → MvPowerSeries (Fin n) Complex)
    (value : (Fin n → Nat) → Complex)
    (m : Nat)
    (S : Finset (Fin n → Nat))
    (hS : ∀ d : Fin n → Nat, d ∈ S ↔ (∑ k, d k) = m)
    (e : Fin n → Nat)
    (he : (∑ k, e k) ≤ m)
    (hterm : ∀ d ∈ S,
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) (f d) =
        (if d = e then value d else 0)) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
      (∑ d ∈ S, f d) =
      (if (∑ k, e k) = m then value e else 0) := by sorry
