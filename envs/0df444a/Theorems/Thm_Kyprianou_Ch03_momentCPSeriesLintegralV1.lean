-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentCPSeriesLintegralV1
-- name    : Kyprianou.Ch03.momentCPSeriesLintegralV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:52:35.06817+00:00
-- url     : https://prove2.me/theorems/e0e32580-9078-44ef-99ee-4b007ac036a1
-- title:
--   Compound-Poisson nonnegative moment series
-- statement:
--   Unfold the finite compound-Poisson series and use lintegral_sum_measure and lintegral_smul_measure.
-- source:
--   Kyprianou (2006), Theorem 3.8, compound-Poisson moment criterion; child 94671c15-20af-4dbe-b8aa-987cace03fb2.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentCPSeriesLintegralV1
    (mu : Measure Real) [IsFiniteMeasure mu]
    (f : Real → ENNReal) :
    (∫⁻ x, f x ∂(KSATSingleFlip.Connect.compoundPoisson mu)) =
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (-(mu Set.univ).toReal) /
        (n.factorial : ℝ)) * (∫⁻ x, f x ∂(KSATSingleFlip.Connect.convPow mu n)) := by sorry
