-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_single_center_series_jet_interpolation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.single_center_series_jet_interpolation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:29:57.442845+00:00
-- url     : https://prove2.me/theorems/5b65c342-210b-4357-952a-f4ffb4a29a85
-- title:
--   Single-center finite-series jet realization
-- statement:
--   At any one center, a polynomial can match an arbitrary formal power series on any specified finite coordinatewise box of coefficients.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.single_center_series_jet_interpolation
    {m : Nat}
    (center : Fin m -> Complex)
    (degree : Fin (m + 1) -> Nat)
    (S : MvPowerSeries (Fin (m + 1)) Complex) :
    Exists fun P : MvPolynomial (Fin (m + 1)) Complex =>
      (e : Fin (m + 1) -> Nat) ->
        ((k : Fin (m + 1)) -> e k <= degree k) ->
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e)
          (formalJet center P) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm e) S := by sorry
