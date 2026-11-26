-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise42AvramLevyTripletBridgeV1
-- name    : Kyprianou.Ch04.exercise42AvramLevyTripletBridgeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T08:33:00.485797+00:00
-- url     : https://prove2.me/theorems/70c94ef5-534a-5015-a4fd-1d5cf6339f12
-- title:
--   Avram BV source gives characteristic Lévy triplet data
-- statement:
--   Construct the general Lévy process and its characteristic triplet from the original stationary independent increments, cadlag paths and positive-real Laplace exponent, identifying the physical BV drift. This is the interface needed to reuse the Proved milestone 1 representation.
-- source:
--   Kyprianou (2006), Exercise 4.2, p. 106 and solution p. 317; deterministic auxiliary or source-law bridge.

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open ProbabilityTheory Set Topology
open scoped Topology
open Kyprianou.Ch04

theorem Kyprianou.Ch04.exercise42AvramLevyTripletBridgeV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
 :
    letI : IsProbabilityMeasure P := L.isProbability
    IsLevyProcess L.X P ∧
    ∃ triplet : LevyKhintchineTriple,
      (∀ (t : NNReal) (xi : Real),
        charFun (P.map (L.X t)) xi =
          Complex.exp (((t : Real) : Complex) *
            Kyprianou.Ch01.levyTripleExponent triplet xi)) ∧
      (triplet.gaussianVariance = 0 ∧
        (∫⁻ y in Set.Ioo (-1 : Real) 1,
          ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤) ∧
      triplet.drift - ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure = L.drift := by
  sorry
