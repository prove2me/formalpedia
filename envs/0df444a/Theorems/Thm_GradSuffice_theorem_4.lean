-- Prove2me | Theorems.Thm_GradSuffice_theorem_4
-- name    : GradSuffice.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:23:20.705925+00:00
-- url     : https://prove2.me/theorems/601a4331-08bb-4a66-bc37-eae6d484fbcc
-- title:
--   Theorem 4, p.10 — shattered trees obstruct optimization: $T_A(\varepsilon)\ge c_\theta(n/\log n)^{1/3}\log(1/\varepsilon)$
-- statement:
--   Let $B$ be the unit ball of a real normed space $X$ and fix a margin $\theta>0$.
--
--   **Theorem 4.** There are $c_\theta>0$ and thresholds $n_0$, $\varepsilon_0>0$, depending only on $\theta$, such that the following holds. If there is a $B^\star$-valued binary tree of depth $n\ge n_0$ shattered by $B$ at margin $\theta$, then for every $0<\varepsilon<\varepsilon_0$ every $\varepsilon$-accurate first-order algorithm $A$, including randomized algorithms, makes
--   $$T_A(\varepsilon)\ \ge\ c_\theta\Big(\frac{n}{\log n}\Big)^{1/3}\log(1/\varepsilon)$$
--   queries. The lower bound holds even when the objectives are required to be continuously differentiable.
--
--   Theorem 4 is the main new implication 1 → 2 of Theorem 1 (by contraposition): an optimizable space cannot shatter arbitrarily deep trees at a fixed margin.
--
--   Differences from the source:
--   - encoding: "for sufficiently large n and sufficiently small ε > 0 … the thresholds on n and ε depend only on θ" → ∃ c_θ > 0, n₀, ε₀ > 0 chosen before the space X, then ∀ n ≥ n₀, 0 < ε < ε₀; reason: quantifier form of the sentence
--   - reading: every ε-accurate algorithm (the lower bound "holds even when the objectives are required to be continuously differentiable") → every algorithm that is ε-accurate on the convex C¹ 1-Lipschitz functions on X answered by their gradient; reason: the last sentence of the theorem; it implies the main sentence, since an ε-accurate algorithm is accurate on these objectives
--   - encoding: T_A(ε) queries, randomized algorithm, Pr → exactly T ≥ 1 queries, a seed space (Ω, μ), measurable success sets; reason: padding by repeating the last query; probabilities of measurable sets
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 4, p.10

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_GradSuffice_IsDualValued
import Definitions.Def_GradSuffice_IsShattered
import Definitions.Def_GradSuffice_IsAccurateC1

namespace GradSuffice

/-- **Theorem 4 (shattered trees obstruct optimization).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 4, p.10: "Let `B` be the unit
ball of a real normed space, and fix a margin `θ > 0`. Suppose there exists a `B⋆`-valued binary tree
of depth `n` shattered by `B` at margin `θ`. Then, for sufficiently large `n` and sufficiently small
`ε > 0`, every ε-accurate first-order optimization algorithm `A`, including randomized algorithms,
requires `T_A(ε) ≥ c_θ (n / log n)^{1/3} log(1/ε)`. Here `c_θ > 0` and the thresholds on `n` and `ε`
depend only on `θ`. The lower bound holds even when the objectives are required to be continuously
differentiable."

**Formalization Note.** `c_θ`, the threshold `n₀` on `n` and `ε₀` on `ε` are chosen before the space
`X`. The algorithm is only required to be ε-accurate on objectives that are convex, `C¹` and
1-Lipschitz on all of `X` (answered by their gradient), which is the last sentence; an algorithm
accurate on all objectives is in particular accurate on these. `log` is the natural logarithm. -/
theorem theorem_4 (θ : ℝ) (hθ : 0 < θ) :
    ∃ cθ : ℝ, 0 < cθ ∧ ∃ n₀ : ℕ, ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] (n : ℕ), n₀ ≤ n →
      ∀ ξ : NondualOpt.Tree (StrongDual ℝ X) n, IsDualValued ξ →
        IsShattered (Metric.closedBall (0 : X) 1) θ ξ →
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ T : ℕ, 0 < T → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure μ] (A : Ω → DetAlg X (Metric.closedBall (0 : X) 1) T),
        IsAccurateC1 (Metric.closedBall (0 : X) 1) ε μ A →
        cθ * ((n : ℝ) / Real.log n) ^ (1 / 3 : ℝ) * Real.log (1 / ε) ≤ T := by sorry

end GradSuffice
