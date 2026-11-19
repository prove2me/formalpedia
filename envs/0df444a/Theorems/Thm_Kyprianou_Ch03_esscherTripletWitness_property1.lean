-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherTripletWitness_property1
-- name    : Kyprianou.Ch03.esscherTripletWitness_property1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-18T15:07:56.944826+00:00
-- url     : https://prove2.me/theorems/117aa0a3-1a20-4f3b-891a-a1afd49d526f
-- title:
--   Theorem 3.9 witness component 1
-- statement:
--   A sound sufficient bridge for the original source, sharing the single Esscher-transformed witness. The conditional premises are supplied by the separate witness-construction theorem.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem esscherTripletWitness_property1
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real)
    (hBeta : IntegrableOn
      (fun x : Real => Real.exp (beta * x))
      {x : Real | 1 <= abs x} T.levyMeasure)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity X beta
                (Real.log
                  (∫ eta, Real.exp (beta * X 1 eta) ∂P))
                t omega) omega ∂P)) :
    forall (Tbeta : ProbabilityTheory.LevyKhintchineTriple),
      (Tbeta.drift =
        T.drift + beta * (T.gaussianVariance : Real) +
          ∫ x in {x : Real | abs x < 1},
            (Real.exp (beta * x) - 1) * x ∂T.levyMeasure ∧ Tbeta.gaussianVariance = T.gaussianVariance ∧ Tbeta.levyMeasure =
        T.levyMeasure.withDensity
          (fun x : Real => ENNReal.ofReal (Real.exp (beta * x)))) ->
      ProbabilityTheory.IsLevyProcess X Q := by
  sorry

end Kyprianou.Ch03
