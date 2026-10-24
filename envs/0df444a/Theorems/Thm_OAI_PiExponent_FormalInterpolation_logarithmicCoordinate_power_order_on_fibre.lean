-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCoordinate_power_order_on_fibre
-- name    : OAI.PiExponent.FormalInterpolation.logarithmicCoordinate_power_order_on_fibre
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:56:41.313369+00:00
-- url     : https://prove2.me/theorems/eb12fea7-0199-4165-90a9-00f6ef9468b9
-- title:
--   A logarithmic coordinate power has the expected fibre order
-- statement:
--   On the fibre `x 0 = 1`, the truncated logarithmic correction evaluates to zero, so the coordinate evaluates to the translated coordinate `x i.succ - c i`. Transcendence makes this nonzero; multiplicativity of the valuation then gives the order of its `e i.succ` power, including exponent zero.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_WeightedIdealCurveCriterion
import Definitions.Def_OAI_PiExponent_LogarithmicCenterIdeals
import Mathlib.FieldTheory.IsAlgClosed.Basic

open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.logarithmicCoordinate_power_order_on_fibre
    {m K : Nat} (c : Fin m → Complex)
    (e : Fin (m + 1) → Nat)
    (E : Type) [Field E] [Algebra Complex E] [Algebra.EssFiniteType Complex E]
    (x : Fin (m + 1) → E) (hfibre : x 0 = 1)
    (hnonconst : ∀ i : Fin m, Transcendental Complex (x i.succ))
    (nu : PolynomialCurvePlace E) (i : Fin m) :
    MvPolynomial.aeval x
        ((logarithmicCoordinate c (fun _ => e 0) i.succ) ^ e i.succ) ≠ 0 ∧
      (polynomialCurveOrder nu
        (MvPolynomial.aeval x
          ((logarithmicCoordinate c (fun _ => e 0) i.succ) ^ e i.succ)) : Real) =
        (e i.succ : Real) *
          (polynomialCurveOrder nu
            (x i.succ - algebraMap Complex E (c i)) : Real) := by sorry
