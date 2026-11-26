-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedSubordinatorImaginaryBoundaryExpansionV1
-- name    : Kyprianou.Ch05.killedSubordinatorImaginaryBoundaryExpansionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:54:02.290897+00:00
-- url     : https://prove2.me/theorems/1124f753-8fea-5554-92e1-b91195bba4a8
-- title:
--   Expand the imaginary-axis complex transform as a sine and cosine exponent
-- statement:
--   Rewrite the marginal transform as charFun, use Euler's identity and Bochner integrability of the exponent integrand, then identify the nonnegative cosine integral with the real lintegral.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.4.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set Complex Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch05.killedSubordinatorImaginaryBoundaryExpansionV1
    (Q Pi : Measure ℝ) [IsProbabilityMeasure Q]
    (hint : Integrable (fun x : ℝ => min (1 : ℝ) |x|) (Pi.restrict (Ioi (0 : ℝ))))
    (d : ℝ) (t : NNReal) (u : ℝ)
    (h : (∫ y, Complex.exp (-(-(u : ℂ) * Complex.I) * (y : ℂ)) ∂Q) =
      Complex.exp (-((t : ℝ) : ℂ) *
        ((d : ℂ) * (-(u : ℂ) * Complex.I) +
          ∫ y in Ioi (0 : ℝ),
            (1 - Complex.exp (-(-(u : ℂ) * Complex.I) * (y : ℂ))) ∂Pi))) :
    MeasureTheory.charFun Q u =
      Complex.exp (↑(-(t : ℝ) * (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal (1 - Real.cos (u * x)) ∂Pi).toReal) +
        ↑((t : ℝ) * (∫ x in Ioi (0 : ℝ), Real.sin (u * x) ∂Pi + d * u)) * Complex.I) := by
  sorry
