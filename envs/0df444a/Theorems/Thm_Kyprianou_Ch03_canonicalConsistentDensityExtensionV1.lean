-- Prove2me | Theorems.Thm_Kyprianou_Ch03_canonicalConsistentDensityExtensionV1
-- name    : Kyprianou.Ch03.canonicalConsistentDensityExtensionV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T17:59:29.376865+00:00
-- url     : https://prove2.me/theorems/ce5a93d8-17ee-412f-a624-8c24a6d7a941
-- title:
--   Kolmogorov extension of consistent finite-horizon densities on zero-origin coordinate paths
-- statement:
--   Consistent nonnegative integrable unit-mass densities on the raw coordinate filtrations extend to a probability measure on the zero-origin product path space. Construct finite-dimensional tilted laws at a dominating time, use their consistency and Kolmogorov extension, and transport to the zero-origin subtype; use uniqueness on cylinder generators for each horizon.
-- source:
--   Kyprianou (2006), Theorem 3.9; decomposition of 24b018f9-56a9-4313-b32a-cb140d602681

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.canonicalConsistentDensityExtensionV1
    (P : Measure {path : NNReal → ℝ // path 0 = 0})
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t omega, X t omega = omega.val t)
    (Z : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hNonneg : ∀ t omega, 0 ≤ Z t omega)
    (hInt : ∀ t, Integrable (Z t) P)
    (hUnit : ∀ t, (∫ omega, Z t omega ∂P) = 1)
    (hCons : ∀ s t : NNReal, s ≤ t → ∀ A,
      MeasurableSet[PerfCorrMSQ.natFiltr X s] A →
      (∫ omega, Set.indicator A (Z t) omega ∂P) =
        (∫ omega, Set.indicator A (Z s) omega ∂P)) :
    ∃ Q : Measure {path : NNReal → ℝ // path 0 = 0},
      Q Set.univ = 1 ∧
      ∀ (t : NNReal) (A : Set {path : NNReal → ℝ // path 0 = 0}),
        MeasurableSet[PerfCorrMSQ.natFiltr X t] A →
          Q A = ENNReal.ofReal
            (∫ omega, Set.indicator A (Z t) omega ∂P) := by sorry
