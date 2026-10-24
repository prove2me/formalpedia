-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_formalJet_logarithmicFrameDerivative_zero_series_chain_rule
-- name    : OAI.PiExponent.FormalInterpolation.formalJet_logarithmicFrameDerivative_zero_series_chain_rule
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:23:46.142765+00:00
-- url     : https://prove2.me/theorems/9c299b5e-4b9b-4562-b89e-3b2927c5a2cd
-- title:
--   Formal jet chain rule for the zeroth logarithmic frame derivative
-- statement:
--   For every m, c, and polynomial F, the formal jet of the zeroth logarithmic frame derivative equals (1 + X₀) times the zeroth formal partial derivative of the formal jet. This follows by applying the substitution chain rule to the images of the polynomial variables; the derivative of each lifted logarithm contributes 1/(1 + X₀), which cancels the prefactor. The statement includes m = 0 and requires no positivity or range hypotheses. This removes the substitution and differentiation calculation from the parent; the concrete proof route is to use the derivation rule for polynomial evaluation, the derivative of `PowerSeries.log`, and compatibility of `liftSeries` with the zeroth partial derivative. This chain rule is the main remaining mathematical obligation.

import Definitions.Def_OAI_PiExponent_LogarithmicWordContact
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPowerSeries.Derivative

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.formalJet_logarithmicFrameDerivative_zero_series_chain_rule {m : Nat} (c : Fin m → Complex) (F : MvPolynomial (Fin (m + 1)) Complex) :
    formalJet c (logarithmicFrameDerivative (0 : Fin (m + 1)) F) =
      ((1 : MvPowerSeries (Fin (m + 1)) Complex) + MvPowerSeries.X (0 : Fin (m + 1))) *
        MvPowerSeries.pderiv Complex (0 : Fin (m + 1)) (formalJet c F) := by sorry
