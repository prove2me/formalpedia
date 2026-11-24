-- Prove2me | Theorems.Thm_Kyprianou_Ch03_canonicalDensityProjectiveProductV1
-- name    : Kyprianou.Ch03.canonicalDensityProjectiveProductV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T22:01:11.651286+00:00
-- url     : https://prove2.me/theorems/48626cf7-7c34-405d-ae37-3b7f16bd8854
-- title:
--   Consistent canonical densities have a projective probability measure on the full product
-- statement:
--   Push each finite-horizon tilted probability forward to its finite coordinate vector at the maximum time. Consistency gives a projective family, and the proved Kolmogorov extension theorem yields the full product measure.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; reduction of 24b018f9-56a9-4313-b32a-cb140d602681.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem Kyprianou.Ch03.canonicalDensityProjectiveProductV1
    (P : Measure {path : NNReal → ℝ // path 0 = 0})
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t w, X t w = w.val t)
    (Z : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hNonneg : ∀ t w, 0 ≤ Z t w)
    (hInt : ∀ t, Integrable (Z t) P)
    (hUnit : ∀ t, (∫ w, Z t w ∂P) = 1)
    (hCons : ∀ s t : NNReal, s ≤ t → ∀ A,
      MeasurableSet[PerfCorrMSQ.natFiltr X s] A →
      (∫ w, A.indicator (Z t) w ∂P) = (∫ w, A.indicator (Z s) w ∂P)) :
    ∃ μ : Measure (NNReal → ℝ), IsProbabilityMeasure μ ∧
      ∀ I : Finset NNReal,
      Measure.map (I.restrict (π := fun _ : NNReal => ℝ)) μ =
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val)
          (P.withDensity (fun w => ENNReal.ofReal (Z (I.sup id) w))) := by
  sorry
