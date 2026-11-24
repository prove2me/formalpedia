-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyJordanSposSnegEqJumpPlusDriftV1
-- name    : Kyprianou.Ch02.bvLevyJordanSposSnegEqJumpPlusDriftV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T13:30:14.581982+00:00
-- url     : https://prove2.me/theorems/0e64aff3-f103-4b9c-b3d3-c0dd968d410e
-- title:
--   Jordan subordinators equal jump sums plus linear drifts
-- statement:
--   Let $X$ be a real Lévy process with locally bounded-variation paths almost surely. Write $V_t$ for the total variation of the path from $0$ to $t$, and set $S^\pm_t=(V_t\pm X_t)/2$ for the canonical Jordan processes. Write $J^\pm_t$ for the cumulative sums of positive and negative jumps of $X$ up to time $t$. Then there exist deterministic nonnegative drift rates $d_+$ and $d_-$ such that almost surely, for every $t\ge 0$,
--   $$
--   S^+_t = J^+_t + d_+ t, \qquad S^-_t = J^-_t + d_- t.
--   $$
--   In other words, the continuous parts of the Jordan subordinators are pure linear drifts, and their jumps coincide with the signed jumps of $X$.
-- source:
--   Kyprianou, Introductory Lectures on Fluctuations of Lévy Processes, Ch.2 Exercise 2.8 / finite-variation Lévy jump-drift representation

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.bvLevyJordanSposSnegEqJumpPlusDriftV1
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
    ∃ dpos dneg : ℝ, 0 ≤ dpos ∧ 0 ≤ dneg ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Spos t ω = Jpos t ω + dpos * (t : ℝ)) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0, Sneg t ω = Jneg t ω + dneg * (t : ℝ)) := by sorry
