-- Prove2me | Theorems.Thm_Kyprianou_Ch03_canonicalFiniteMarginalLimitV1
-- name    : Kyprianou.Ch03.canonicalFiniteMarginalLimitV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T23:03:26.833503+00:00
-- url     : https://prove2.me/theorems/fc9f7374-6f9e-4711-bd10-4f7b0c45472d
-- title:
--   Projective limit of finite-dimensional consistent raw probability laws
-- statement:
--   At each finite set of coordinates choose its supremum time and push forward the corresponding probability law. The past-consistency assumption makes these marginals projective and independent of the choice of dominating time. Apply the proved Kolmogorov extension theorem.
-- source:
--   Kyprianou (2006), Chapter 3, Theorem 3.9; decomposition of ce5a93d8-17ee-412f-a624-8c24a6d7a941

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.canonicalFiniteMarginalLimitV1
    {Ω : Type} [MeasurableSpace Ω]
    (X : NNReal → Ω → ℝ) (hX : ∀ t, Measurable (X t))
    (D : NNReal → Measure Ω) (hUnit : ∀ t, D t Set.univ = 1)
    (hCons : ∀ s t : NNReal, s ≤ t → ∀ A,
      MeasurableSet[PerfCorrMSQ.natFiltr X s] A → D t A = D s A) :
    ∃ M : Measure (NNReal → ℝ), M Set.univ = 1 ∧
      ∀ (t : NNReal) (J : Finset NNReal), (∀ j ∈ J, j ≤ t) →
        M.map (fun path (j : J) => path j.val) =
          (D t).map (fun w (j : J) => X j.val w) := by sorry
