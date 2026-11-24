-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevySubordinatorEqJumpSumPlusDriftV1
-- name    : Kyprianou.Ch02.bvLevySubordinatorEqJumpSumPlusDriftV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T17:23:11.457361+00:00
-- url     : https://prove2.me/theorems/1d5a66b1-d7ab-473c-92ad-986bf72edbec
-- title:
--   Lévy subordinator equals jump sum plus linear drift
-- statement:
--   Let $Y$ be a real Lévy process whose paths are almost surely monotone (a Lévy subordinator, allowing a possible negative starting convention only through the Lévy axioms). Write
--   $$
--   J_t(\omega)=\sum_{0<s\le t}\max\bigl(Y_s(\omega)-Y_{s-}(\omega),0\bigr)
--   $$
--   for the cumulative sum of its positive jumps (implemented via `∑'` over `Set.Ioc 0 t` and left limits). Then there exists a deterministic drift rate $d\ge 0$ such that almost surely, for every $t\ge 0$,
--   $$
--   Y_t = d\,t + J_t.
--   $$
--   In other words, the continuous part of a Lévy subordinator is a pure linear drift.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 2, Lemma 2.12 / Exercise 2.8, pp. 54-59

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevySubordinatorEqJumpSumPlusDriftV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℝ≥0 → Ω → ℝ)
    (hY : ProbabilityTheory.IsLevyProcess Y P)
    (hMono : ∀ᵐ ω ∂P, Monotone (fun t => Y t ω)) :
    ∃ d : ℝ, 0 ≤ d ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Y t ω =
          d * (t : ℝ) +
            ∑' s : Set.Ioc (0 : ℝ≥0) t,
              max (Y s.1 ω -
                Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => Y u ω)) 0 := by sorry
