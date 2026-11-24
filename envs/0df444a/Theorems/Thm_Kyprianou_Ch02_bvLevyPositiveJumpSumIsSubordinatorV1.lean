-- Prove2me | Theorems.Thm_Kyprianou_Ch02_bvLevyPositiveJumpSumIsSubordinatorV1
-- name    : Kyprianou.Ch02.bvLevyPositiveJumpSumIsSubordinatorV1
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T22:42:52.494963+00:00
-- url     : https://prove2.me/theorems/7ec60bc0-f6ad-4a7f-88c0-9e0dc087ec60
-- title:
--   Positive jump-sum process of a bounded-variation Lévy process is a subordinator
-- statement:
--   Let $(\Omega, \mathcal{F}, P)$ be a probability space carrying a real-valued Lévy process $X = (X_t)_{t \ge 0}$ whose sample paths have locally bounded variation on $[0, \infty)$ almost surely. For each $t \ge 0$ and $\omega \in \Omega$, define the cumulative positive jump process
--
--   $$
--   J_t^+(\omega) := \sum_{0 < s \le t} \max\bigl(X_s(\omega) - X_{s-}(\omega),\, 0\bigr),
--   $$
--
--   where $X_{s-}(\omega) := \lim_{u \uparrow s} X_u(\omega)$ denotes the left limit of the path at time $s > 0$.
--
--   Then $J^+ = (J_t^+)_{t \ge 0}$ is a Lévy process on $(\Omega, P)$ whose sample paths $t \mapsto J_t^+(\omega)$ are nondecreasing almost surely (i.e., $J^+$ is a subordinator).
--
--   This isolates the pathwise and distributional subordinator property of the positive jump sum of a bounded-variation Lévy process, which applies symmetrically to $-X$ to yield the negative jump-sum subordinator $J^-$.
--
--   **Formalization Note** Left limits are encoded via `Filter.limUnder (nhdsWithin s (Set.Iio s)) (fun u => X u ω)` and the jump sum via `tsum` over `Set.Ioc (0 : ℝ≥0) t`, which vanishes identically at $t = 0$ since `Set.Ioc (0 : ℝ≥0) 0` is empty.
-- source:
--   Kyprianou (2006), Introductory Lectures on Fluctuations of Lévy Processes with Applications, Chapter 2, Section 2.5 & Exercise 2.8, pp. 55-59

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch02

theorem bvLevyPositiveJumpSumIsSubordinatorV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P,
      LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let Jpos : ℝ≥0 → Ω → ℝ := fun t ω =>
      ∑' s : Set.Ioc (0 : ℝ≥0) t,
        max (X s.1 ω -
          Filter.limUnder (nhdsWithin s.1 (Set.Iio s.1)) (fun u => X u ω)) 0
    ProbabilityTheory.IsLevyProcess Jpos P ∧
    (∀ᵐ ω ∂P, Monotone (fun t => Jpos t ω)) := by sorry

end Kyprianou.Ch02
