-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_sheared_substitution_formula
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_sheared_substitution_formula
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T06:28:48.28222+00:00
-- url     : https://prove2.me/theorems/66d19184-89ad-4aef-9d92-495cecd10cf1
-- title:
--   Formula for the composed sheared substitution
-- statement:
--   After the specified polynomial substitution and application of `formalJet`, the resulting series is polynomial evaluation at `X 0` for the first variable and `X i.succ + liftLogSeries m (PowerSeries.log ℂ) - X 0` for each later variable.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open scoped BigOperators
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_sheared_substitution_formula
    {m : Nat}
    (center : Fin m -> Complex)
    (Q : MvPolynomial (Fin (m + 1)) Complex) :
    formalJet center (MvPolynomial.aeval
      (Fin.cases (MvPolynomial.X 0 - MvPolynomial.C 1)
        (fun i => MvPolynomial.X i.succ - MvPolynomial.C (center i) -
          (MvPolynomial.X 0 - MvPolynomial.C 1))) Q) =
      MvPolynomial.aeval
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ +
            liftLogSeries m (PowerSeries.log ℂ) - MvPowerSeries.X 0)) Q := by sorry
