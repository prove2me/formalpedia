-- Prove2me | Theorems.Thm_Kyprianou_Ch02_levyBoundedContinuousVanishingNearZeroIntegrableV1
-- name    : Kyprianou.Ch02.levyBoundedContinuousVanishingNearZeroIntegrableV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:55:37.981642+00:00
-- url     : https://prove2.me/theorems/154626db-dc8a-425b-ad57-6cffdb15d561
-- title:
--   A bounded continuous function vanishing near zero is integrable under a Lévy measure
-- statement:
--   Restrict the Lévy measure to the finite-intensity region |x|≥r and use boundedness and continuity for integrability. Extend by zero since the function vanishes on the complementary small marks.
-- source:
--   Kyprianou (2006), Chapter 2, Lemma 2.14; small-time marginal test necessity, parent cee5c65f-db82-4515-8f93-f2ed6c878db1.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem Kyprianou.Ch02.levyBoundedContinuousVanishingNearZeroIntegrableV1
    (ν : Measure ℝ) (hν : ProbabilityTheory.IsLevyMeasure ν)
    (f : BoundedContinuousFunction ℝ ℝ) (r : ℝ) (hr : 0 < r)
    (hf : ∀ x : ℝ, |x| < r → f x = 0) :
    Integrable (fun x : ℝ => f x) ν := by sorry
