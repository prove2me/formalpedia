-- Prove2me | Theorems.Thm_Kyprianou_Ch03_canonicalProbabilityFromMarginalLimitV1
-- name    : Kyprianou.Ch03.canonicalProbabilityFromMarginalLimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:03:26.602673+00:00
-- url     : https://prove2.me/theorems/ca77e4cc-14b8-48ec-956e-e882b290176f
-- title:
--   Raw canonical probability law recovered from the finite-dimensional limit
-- statement:
--   The full product measure is concentrated on zero-origin paths by the zero coordinate marginal. Push it to the zero-origin subtype, and compare each horizon-restricted product law with the corresponding finite-horizon probability law using uniqueness from finite-dimensional marginals.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; decomposition of ce5a93d8-17ee-412f-a624-8c24a6d7a941

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.canonicalProbabilityFromMarginalLimitV1
    (X : NNReal → {path : NNReal → ℝ // path 0 = 0} → ℝ)
    (hCoordinate : ∀ t w, X t w = w.val t)
    (D : NNReal → Measure {path : NNReal → ℝ // path 0 = 0})
    (hUnit : ∀ t, D t Set.univ = 1)
    (M : Measure (NNReal → ℝ)) (hM : M Set.univ = 1)
    (hMarg : ∀ (t : NNReal) (J : Finset NNReal), (∀ j ∈ J, j ≤ t) →
        M.map (fun path (j : J) => path j.val) =
          (D t).map (fun w (j : J) => X j.val w)) :
    ∃ Q : Measure {path : NNReal → ℝ // path 0 = 0},
      Q Set.univ = 1 ∧ ∀ (t : NNReal) A,
        MeasurableSet[PerfCorrMSQ.natFiltr X t] A → Q A = D t A := by sorry
