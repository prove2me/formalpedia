-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_Xprod_pow_eq_monomial
-- name    : OAI.PiExponent.LogarithmicJetIdeals.Xprod_pow_eq_monomial
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T21:59:55.127388+00:00
-- url     : https://prove2.me/theorems/49c8c286-0c86-40ea-9360-a5a8613f8510
-- title:
--   Finite product of formal variable powers is a monomial
-- statement:
--   The product, over all coordinates, of each formal variable raised to its prescribed natural exponent, multiplied by a scalar, is the formal monomial with that exponent function and coefficient. Zero exponents contribute one, including when every exponent is zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_PlainJet
import Mathlib.Data.Fintype.Pi

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.Xprod_pow_eq_monomial
    {m : Nat} (a : Complex) (d : Fin (m + 1) -> Nat) :
    MvPowerSeries.C a *
        Finset.prod Finset.univ (fun k : Fin (m + 1) =>
          (MvPowerSeries.X k) ^ d k) =
      MvPowerSeries.monomial (Finsupp.equivFunOnFinite.symm d) a := by sorry
