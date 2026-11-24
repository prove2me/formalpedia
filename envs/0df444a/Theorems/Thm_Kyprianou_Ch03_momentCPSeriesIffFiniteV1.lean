-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentCPSeriesIffFiniteV1
-- name    : Kyprianou.Ch03.momentCPSeriesIffFiniteV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:52:34.173935+00:00
-- url     : https://prove2.me/theorems/12cfbd6e-2373-4aa9-a901-54e548cf3855
-- title:
--   Finiteness of the compound-Poisson moment series iff the mark moment is finite
-- statement:
--   For necessity use the strictly positive n=1 coefficient. For sufficiency combine geometric convolution bounds and the Poisson weighted geometric sum.
-- source:
--   Kyprianou (2006), Theorem 3.8, compound-Poisson moment criterion; child 94671c15-20af-4dbe-b8aa-987cace03fb2.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentCPSeriesIffFiniteV1
    (mu : Measure Real) [IsFiniteMeasure mu]
    (g : Real → Real) (hg : Kyprianou.Ch03.IsSubmultiplicative g)
    (hg_meas : Measurable g) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂(KSATSingleFlip.Connect.compoundPoisson mu)) < ⊤ ↔
      (∫⁻ x, ENNReal.ofReal (g x) ∂mu) < ⊤ := by sorry
