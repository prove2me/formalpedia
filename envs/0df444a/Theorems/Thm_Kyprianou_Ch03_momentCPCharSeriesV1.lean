-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentCPCharSeriesV1
-- name    : Kyprianou.Ch03.momentCPCharSeriesV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T13:16:16.061078+00:00
-- url     : https://prove2.me/theorems/264faac9-5ef8-4922-83bd-9bd7c526e452
-- title:
--   Characteristic function of compound-Poisson law as weighted power series
-- statement:
--   Use the probability of the compound-Poisson law to integrate its bounded Fourier character. Integrate termwise over the defining measure sum and use the convolution power characteristic function.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; decomposition of compound-Poisson characteristic function and compensated exponential kernel.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentCPCharSeriesV1
    (mu : Measure Real) [IsFiniteMeasure mu] (xi : Real) :
    charFun (KSATSingleFlip.Connect.compoundPoisson mu) xi =
      ∑' n : ℕ, ((Real.exp (-(mu Set.univ).toReal) : ℝ) : ℂ) *
        ((charFun mu xi) ^ n / (n.factorial : ℂ)) := by sorry
