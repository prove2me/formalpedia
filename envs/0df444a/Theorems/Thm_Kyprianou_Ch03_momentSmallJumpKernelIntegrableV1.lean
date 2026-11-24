-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentSmallJumpKernelIntegrableV1
-- name    : Kyprianou.Ch03.momentSmallJumpKernelIntegrableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:35:22.022603+00:00
-- url     : https://prove2.me/theorems/77a7897f-66c5-4581-a28c-2724454fdef9
-- title:
--   Quadratic compensated exponential kernel on the small-jump region
-- statement:
--   Taylor's formula with a bounded second derivative on the unit interval gives a constant times x² bound for the nonnegative kernel. Apply the Lévy-measure integrability of min(1,x²) on this interval.
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

theorem Kyprianou.Ch03.momentSmallJumpKernelIntegrableV1
    (T : ProbabilityTheory.LevyKhintchineTriple) (b : Real) :
    IntegrableOn (fun x : Real => Real.exp (b * x) - 1 - b * x)
      (Set.Ioo (-1 : Real) 1) T.levyMeasure := by sorry
