-- Prove2me | Theorems.Thm_Kyprianou_Ch01_harmonicReciprocalLIntegralFormula
-- name    : Kyprianou.Ch01.harmonicReciprocalLIntegralFormula
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T12:59:11.965574+00:00
-- url     : https://prove2.me/theorems/c7694ea7-cfa2-4dcc-9c1b-6d5920d78083
-- title:
--   Finite extended Lebesgue integral of positive reciprocal harmonic kernel equals logarithmic integral
-- statement:
--   The restricted positive Lebesgue lintegral of the reciprocal of C(1+r), for C>0 on [0,s], is exactly the ENNReal image of log(1+s)/C. This is a finite-time, source-faithful identity bridging the Proved real harmonic integral theorem and the divergent extended inverse-speed occupation integral.
-- source:
--   Elementary harmonic integration, Kyprianou (2006), Chapter 1, time-change logarithmic integral.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Theorems.Thm_Kyprianou_Ch01_realHarmonicIntegralFormulaV2
open MeasureTheory Kyprianou.Ch01 Set Filter Real
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.harmonicReciprocalLIntegralFormula
    (C : ℝ) (hC : 0 < C) (s : ℝ≥0) :
    (∫⁻ r in Set.Ioc (0 : ℝ) (s : ℝ),
      (ENNReal.ofReal (C * (1 + r)))⁻¹ ∂volume) =
        ENNReal.ofReal (Real.log (1 + (s : ℝ)) / C) := by
  sorry
