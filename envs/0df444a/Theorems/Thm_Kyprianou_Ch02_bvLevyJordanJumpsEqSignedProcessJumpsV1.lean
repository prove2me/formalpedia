-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyJordanJumpsEqSignedProcessJumpsV1
-- name    : Kyprianou.Ch02.bvLevyJordanJumpsEqSignedProcessJumpsV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T17:23:14.291836+00:00
-- url     : https://prove2.me/theorems/7ccedcbf-e1dc-4e69-94f2-d379f9c298ec
-- title:
--   Jordan process jumps equal signed jumps of $X$
-- statement:
--   Let $X$ be a real Lévy process of locally bounded variation, with canonical Jordan processes $S^\pm_t=(V_t\pm X_t)/2$. Write $J^\pm$ for the cumulative positive/negative jump sums of $X$, and $J(S^\pm)$ for the analogous positive jump sums of the paths of $S^\pm$. Then almost surely, for every $t\ge 0$,
--   $$
--   J(S^+)_t = J^+_t, \qquad J(S^-)_t = J^-_t.
--   $$
--   That is, the jumps of the Jordan subordinators are exactly the signed jumps of $X$.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 2, Lemma 2.12 / Exercise 2.8, pp. 54-59

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyJordanJumpsEqSignedProcessJumpsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s : ℝ≥0 => X s ω) Set.univ 0 t
    let Spos : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let Sneg : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (X s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
    let Jneg : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω) -
          X s.1 ω) 0
    let JSpos : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Spos s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Spos u ω)) 0
    let JSneg : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Sneg s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Sneg u ω)) 0
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, JSpos t ω = Jpos t ω) ∧
    (∀ᵐ ω ∂P, ∀ t : ℝ≥0, JSneg t ω = Jneg t ω) := by sorry
