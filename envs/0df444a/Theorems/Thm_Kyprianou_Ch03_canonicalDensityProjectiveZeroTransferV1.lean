-- Prove2me | Theorems.Thm_Kyprianou_Ch03_canonicalDensityProjectiveZeroTransferV1
-- name    : Kyprianou.Ch03.canonicalDensityProjectiveZeroTransferV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T22:00:58.736049+00:00
-- url     : https://prove2.me/theorems/1f57c6f7-f232-40ea-950b-06c9e51a7481
-- title:
--   Projective tilted product law transfers to zero-origin paths
-- statement:
--   The time-zero marginal forces the full product law to have zero origin almost surely. Patch the zero coordinate on exceptional paths and transport to the subtype. Finite cylinder identities determine equality on each raw past sigma algebra.
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

theorem Kyprianou.Ch03.canonicalDensityProjectiveZeroTransferV1
    (P : Measure {path : NNReal → ℝ // path 0 = 0})
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t w, X t w = w.val t)
    (Z : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hNonneg : ∀ t w, 0 ≤ Z t w)
    (hInt : ∀ t, Integrable (Z t) P)
    (hUnit : ∀ t, (∫ w, Z t w ∂P) = 1)
    (hCons : ∀ s t : NNReal, s ≤ t → ∀ A,
      MeasurableSet[PerfCorrMSQ.natFiltr X s] A →
      (∫ w, A.indicator (Z t) w ∂P) = (∫ w, A.indicator (Z s) w ∂P))
    (μ : Measure (NNReal → ℝ)) [IsProbabilityMeasure μ]
    (hProj : ∀ I : Finset NNReal,
      Measure.map (I.restrict (π := fun _ : NNReal => ℝ)) μ =
        Measure.map (fun w : {path : NNReal → ℝ // path 0 = 0} => I.restrict w.val)
          (P.withDensity (fun w => ENNReal.ofReal (Z (I.sup id) w)))) :
    ∃ Q : Measure {path : NNReal → ℝ // path 0 = 0}, Q Set.univ = 1 ∧
      ∀ (t : NNReal) (A : Set {path : NNReal → ℝ // path 0 = 0}),
        MeasurableSet[PerfCorrMSQ.natFiltr X t] A →
        Q A = ENNReal.ofReal (∫ w, A.indicator (Z t) w ∂P) := by
  sorry
