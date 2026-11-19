-- Prove2me | Theorems.Thm_HelfgottZeroCertificate_continuous_phase_abs_grid_variation_le
-- name    : HelfgottZeroCertificate.continuous_phase_abs_grid_variation_le
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-18T11:59:48.12803+00:00
-- url     : https://prove2.me/theorems/4dc400ae-60d9-4929-a7e3-968d6712cc3a
-- title:
--   Endpoint phase variation bounded by the number of crossings of an arithmetic grid
-- statement:
--   Let $\theta$ be a continuous real-valued function on the closed interval with endpoints $a,b$. Let $p>0$ and $c\in\mathbb R$, and suppose a finite set $Z\subset\mathbb R$ contains every point $t$ in that interval at which $\theta(t)=c+kp$ for some integer $k$. Then
--
--   $$|\theta(b)-\theta(a)|\le p(|Z|+1).$$
--
--   No monotonicity of $\theta$ is required. The result controls endpoint phase change using finitely many level-crossing points, and is useful when these points are detected by zeros of an auxiliary real function.
-- source:
--   Original formalization developed for explicit zero-count estimates in the Prove2Me Weak Goldbach project. Source upstream/Solutions/ContinuousPhaseZeroCount.lean; SHA256 3a48cf3fbbd812e4d4fdcb848266a05c184ea85ba50de16231c0450edd08ee53. Supporting proof is included in the immutable solution submission. Standard arctangent integration / intermediate-value arguments; no claim of a new mathematical theorem.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
open Set
open scoped BigOperators

theorem HelfgottZeroCertificate.continuous_phase_abs_grid_variation_le :
∀ {θ : ℝ → ℝ} {a b c p : ℝ},
  0 < p →
    ContinuousOn θ (Set.uIcc a b) →
      ∀ (Z : Finset ℝ), (∀ t ∈ Set.uIcc a b, ∀ (k : ℤ), θ t = c + ↑k * p → t ∈ Z) → |θ b - θ a| ≤ p * (↑Z.card + 1) := by sorry
