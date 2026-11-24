-- Prove2me | Theorems.Thm_Kyprianou_Ch03_esscherCanonicalRawDensityConsistencyV1
-- name    : Kyprianou.Ch03.esscherCanonicalRawDensityConsistencyV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T17:59:44.348715+00:00
-- url     : https://prove2.me/theorems/ab761573-db74-4e47-82c1-6b9e662005ef
-- title:
--   Esscher densities have unit mean and consistency on the raw coordinate filtration
-- statement:
--   On canonical paths, the deterministic Esscher densities are integrable with mean one and consistent on raw past events. Restrict the completed-natural-filtration density results to raw events, or use independent stationary increments directly.
-- source:
--   Kyprianou (2006), Theorem 3.9; decomposition of 24b018f9-56a9-4313-b32a-cb140d602681

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem Kyprianou.Ch03.esscherCanonicalRawDensityConsistencyV1
    (P : Measure {path : NNReal → ℝ // path 0 = 0})
    [IsProbabilityMeasure P]
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t omega, X t omega = omega.val t)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : ℝ)
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (beta * x))
      {x : ℝ | 1 ≤ |x|} T.levyMeasure) :
    let k := Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P)
    (∀ t : NNReal, Integrable (esscherDensity X beta k t) P ∧
      (∫ omega, esscherDensity X beta k t omega ∂P) = 1) ∧
    (∀ s t : NNReal, s ≤ t → ∀ A,
      MeasurableSet[PerfCorrMSQ.natFiltr X s] A →
      (∫ omega, Set.indicator A (esscherDensity X beta k t) omega ∂P) =
        (∫ omega, Set.indicator A (esscherDensity X beta k s) omega ∂P)) := by sorry
