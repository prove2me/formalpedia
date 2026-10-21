-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finiteJet_comp_surjective
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finiteJet_comp_surjective
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T06:08:40.773712+00:00
-- url     : https://prove2.me/theorems/3e256edb-3551-46fb-b5f8-5afa76632bc8
-- title:
--   Finite jet interpolation for identity-linear formal coordinates
-- statement:
--   Formal coordinates with zero constant terms and identity linear coefficients allow polynomial interpolation of arbitrary coefficients through total degree N.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.finiteJet_comp_surjective
    {n : Nat}
    (phi : Fin n → MvPowerSeries (Fin n) Complex)
    (hzero : ∀ i, MvPowerSeries.coeff 0 (phi i) = 0)
    (hlinear : ∀ i j, MvPowerSeries.coeff (Finsupp.single j 1) (phi i) =
      (if i = j then 1 else 0))
    (N : Nat)
    (value : (Fin n → Nat) → Complex) :
    Exists fun Q : MvPolynomial (Fin n) Complex =>
      (e : Fin n → Nat) →
        (∑ k, e k) ≤ N →
          MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
            (MvPolynomial.aeval phi Q) = value e := by sorry
