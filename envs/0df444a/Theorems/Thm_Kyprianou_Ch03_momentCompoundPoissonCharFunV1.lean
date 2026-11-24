-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentCompoundPoissonCharFunV1
-- name    : Kyprianou.Ch03.momentCompoundPoissonCharFunV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:35:14.895666+00:00
-- url     : https://prove2.me/theorems/4e65cfd0-5116-4661-a0d3-feb0fbfc13eb
-- title:
--   Characteristic function of the finite compound-Poisson series
-- statement:
--   Use the explicit Poisson series of convolution powers. Integrate the bounded Fourier character termwise, evaluate the character of each convolution power, and sum the exponential series.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8: finite compound-Poisson law and exponential moment of the compensated small-jump law.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentCompoundPoissonCharFunV1
    (mu : Measure Real) [IsFiniteMeasure mu] (xi : Real) :
    charFun (KSATSingleFlip.Connect.compoundPoisson mu) xi =
      Complex.exp (∫ x, (Complex.exp (Complex.I * (((xi * x : Real) : Complex))) - 1) ∂mu) := by sorry
