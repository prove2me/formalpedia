-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyJordanJumpIdentityPointwiseV1
-- name    : Kyprianou.Ch02.bvLevyJordanJumpIdentityPointwiseV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T22:33:39.326257+00:00
-- url     : https://prove2.me/theorems/6562d889-d68d-4c99-bc82-3bcf857b9dee
-- title:
--   Jordan jumps equal signed jumps of $X$ pointwise
-- statement:
--   Let $X$ be a càdlàg path of locally bounded variation, with Jordan processes $S^\pm=(V\pm X)/2$. At every time $s$, the positive jump of $S^+$ equals the positive jump of $X$, and the positive jump of $S^-$ equals the negative jump of $X$.
-- source:
--   Kyprianou (2006), Ch.2, Lemma 2.12 / Exercise 2.8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyJordanJumpIdentityPointwiseV1
    (X : ℝ≥0 → ℝ) (s : ℝ≥0)
    (hBV : LocallyBoundedVariationOn X Set.univ)
    (hcad : ProbabilityTheory.IsCadlag X) :
    let V := fun t => variationOnFromTo X Set.univ 0 t
    let Spos := fun t => (V t + X t) / 2
    let Sneg := fun t => (V t - X t) / 2
    let Δ : (ℝ≥0 → ℝ) → ℝ := fun Z =>
      Z s - Filter.limUnder (nhdsWithin s (Set.Iio s)) Z
    max (Δ Spos) 0 = max (Δ X) 0 ∧
    max (Δ Sneg) 0 = max (-Δ X) 0 := by sorry
