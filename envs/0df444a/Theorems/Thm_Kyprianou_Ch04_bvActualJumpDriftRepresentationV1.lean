-- Prove2me | Theorems.Thm_Kyprianou_Ch04_bvActualJumpDriftRepresentationV1
-- name    : Kyprianou.Ch04.bvActualJumpDriftRepresentationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T22:01:14.271727+00:00
-- url     : https://prove2.me/theorems/fa06618c-9b2e-4ec7-b22e-469d241e3947
-- title:
--   Actual jumps and identified drift of a bounded-variation Levy path
-- statement:
--   Transfer the canonical finite-first-moment Poisson path representation to the given cadlag Levy law, identify the compensated drift, and identify the jumps with the specified left limits.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.2, p. 91; source-faithful auxiliary obligation.

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LeanLevy_Levy_LevyKhintchine
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch04

theorem Kyprianou.Ch04.bvActualJumpDriftRepresentationV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hLevy : ProbabilityTheory.IsLevyProcess X P)
    (triplet : ProbabilityTheory.LevyKhintchineTriple)
    (hTriplet : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent triplet xi))
    (hBV : triplet.gaussianVariance = 0 ∧
      (∫⁻ y in Set.Ioo (-1 : Real) 1,
        ENNReal.ofReal |y| ∂triplet.levyMeasure) < ⊤)
    (Xleft : NNReal → Omega → Real)
    (hLeft : ∀ᵐ omega : Omega ∂P, forall t : NNReal,
      0 < t →
        Tendsto (fun s : NNReal => X s omega)
          (nhdsWithin t (Set.Iio t))
          (nhds (Xleft t omega))) :
    ∀ᵐ omega : Omega ∂P, forall t : NNReal,
      Summable (fun s : Set.Ioc (0 : NNReal) t => |X s omega - Xleft s omega|) ∧
      X t omega = X 0 omega + (triplet.drift - ∫ y in Set.Ioo (-1 : Real) 1, y ∂triplet.levyMeasure) * (t : Real) +
        ∑' s : Set.Ioc (0 : NNReal) t, (X s omega - Xleft s omega) := by
  sorry
