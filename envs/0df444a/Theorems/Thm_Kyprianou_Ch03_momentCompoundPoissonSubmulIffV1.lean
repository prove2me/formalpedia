-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentCompoundPoissonSubmulIffV1
-- name    : Kyprianou.Ch03.momentCompoundPoissonSubmulIffV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T12:35:07.098274+00:00
-- url     : https://prove2.me/theorems/94671c15-20af-4dbe-b8aa-987cace03fb2
-- title:
--   Finite compound-Poisson series preserves submultiplicative integrability
-- statement:
--   Use the positive coefficient of the single-jump convolution power for necessity. For sufficiency, bound the nonnegative lintegral of g on each convolution power recursively by the previous integral times the finite integral of c*g; the resulting exponential series is finite.
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

theorem Kyprianou.Ch03.momentCompoundPoissonSubmulIffV1
    (mu : Measure Real) [IsFiniteMeasure mu]
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g) :
    Integrable g (KSATSingleFlip.Connect.compoundPoisson mu) ↔ Integrable g mu := by sorry
