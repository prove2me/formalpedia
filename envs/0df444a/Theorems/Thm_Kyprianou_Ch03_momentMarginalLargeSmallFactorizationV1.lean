-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentMarginalLargeSmallFactorizationV1
-- name    : Kyprianou.Ch03.momentMarginalLargeSmallFactorizationV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T12:30:27.278961+00:00
-- url     : https://prove2.me/theorems/eaabed97-7a10-4b6b-9d55-ec368594a118
-- title:
--   Large-jump and light-tailed marginal factorisation
-- statement:
--   Construct the large-jump law and the Gaussian, drift, compensated-small-jump law using the Lévy–Itô decomposition (or split triplets). Their characteristic functions multiply by the proved source-faithful exponent algebra, and characteristic-function uniqueness identifies the product sum law.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; shared reduction of submulMoment_forward and submulMoment_reverse.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentMarginalLargeSmallFactorizationV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : Real) : Complex) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (t : NNReal) (ht : 0 < t) :
    ∃ (mu nu : Measure Real), IsProbabilityMeasure mu ∧ IsProbabilityMeasure nu ∧
      P.map (X t) = (mu.prod nu).map (fun p : Real × Real => p.1 + p.2) ∧
      (∀ xi : Real, charFun mu xi = Complex.exp (((t : Real) : Complex) *
        ∫ x in {x : Real | 1 ≤ |x|},
          (Complex.exp (Complex.I * (((xi * x : Real) : Complex))) - 1) ∂T.levyMeasure)) ∧
      (∀ xi : Real, charFun nu xi = Complex.exp (((t : Real) : Complex) *
          (Complex.I * ((T.drift * xi : Real) : Complex) -
          (((T.gaussianVariance : Real) * xi ^ 2 / 2 : Real) : Complex) +
          ∫ x in Set.Ioo (-1 : Real) 1,
            ProbabilityTheory.levyCompensatedIntegrand xi x ∂T.levyMeasure))) := by sorry
