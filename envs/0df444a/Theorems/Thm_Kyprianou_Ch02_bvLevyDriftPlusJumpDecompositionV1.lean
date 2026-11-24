-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyDriftPlusJumpDecompositionV1
-- name    : Kyprianou.Ch02.bvLevyDriftPlusJumpDecompositionV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T22:43:23.201801+00:00
-- url     : https://prove2.me/theorems/f83dd76d-c53b-40ae-ac8c-9cd9725c0370
-- title:
--   Deterministic drift plus signed jump-sum representation of a bounded-variation Lévy process
-- statement:
--   Let $(\Omega, \mathcal{F}, P)$ be a probability space carrying a real-valued Lévy process $X = (X_t)_{t \ge 0}$ whose sample paths have locally bounded variation on $[0, \infty)$ almost surely. Define the cumulative positive and negative jump processes
--
--   $$
--   J_t^+(\omega) := \sum_{0 < s \le t} \max\bigl(X_s(\omega) - X_{s-}(\omega),\, 0\bigr), \qquad
--   J_t^-(\omega) := \sum_{0 < s \le t} \max\bigl(X_{s-}(\omega) - X_s(\omega),\, 0\bigr).
--   $$
--
--   Then there exists a deterministic drift constant $d \in \mathbb{R}$ such that almost surely, for all $t \ge 0$,
--
--   $$
--   X_t(\omega) = d\, t + J_t^+(\omega) - J_t^-(\omega).
--   $$
--
--   This expresses the Lévy–Itô pathwise representation of a bounded-variation Lévy process (no Brownian component and absolutely summable jumps) directly on the original probability space $(\Omega, P)$.
--
--   **Formalization Note** Left limits are represented via `Filter.limUnder (nhdsWithin s (Set.Iio s)) (fun u => X u ω)` and cumulative jump sums via `tsum` over `Set.Ioc (0 : ℝ≥0) t`.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 2, Lemma 2.12 & Exercise 2.8, pp. 54-59

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem bvLevyDriftPlusJumpDecompositionV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (X s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
    let Jneg : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω) -
          X s.1 ω) 0
    ∃ d : ℝ, ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X t ω = d * (t : ℝ) + Jpos t ω - Jneg t ω := by sorry

end Kyprianou.Ch02
