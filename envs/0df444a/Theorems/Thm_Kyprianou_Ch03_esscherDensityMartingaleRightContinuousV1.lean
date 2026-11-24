-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherDensityMartingaleRightContinuousV1
-- name    : Kyprianou.Ch03.esscherDensityMartingaleRightContinuousV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T15:13:46.632779+00:00
-- url     : https://prove2.me/theorems/7ba9c068-98f7-4ef1-acb8-aafbf1f7c8c0
-- title:
--   Esscher density martingale and right continuity
-- statement:
--   Deterministic consistency and adaptedness imply the exponential density martingale; cadlag paths give right continuity.
-- source:
--   Kyprianou (2006), Corollary 3.11; faithful support for e939e617-26cc-4e11-98c6-e87492aefbb3

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

open Filter
open scoped Topology

theorem Kyprianou.Ch03.esscherDensityMartingaleRightContinuousV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
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
    : let k := Real.log (∫ w, Real.exp (beta * X 1 w) ∂P)
    let Z := esscherDensity X beta k
    Martingale Z F P ∧
      (∀ᵐ w ∂P, ∀ t : NNReal, ContinuousWithinAt (fun u => Z u w) (Set.Ici t) t) := by sorry
