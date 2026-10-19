-- Prove2me | Theorems.Thm_OAI_RadialTransition_multiscale_pressure_balls
-- name    : OAI.RadialTransition.multiscale_pressure_balls
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:06:49.067019+00:00
-- url     : https://prove2.me/theorems/0e9aa5ee-39a7-4cd3-b45a-fd41f889f9bb
-- title:
--   Multiscale iteration of ideal attraction transforms keeps a ball of supporting slopes (OpenAI, radial phase transition)
-- statement:
--   This is an abstract iteration lemma about pressures, meaning functions $P : \mathbb{R}^2 \to \mathbb{R}$ of $(\beta, h)$ (`Pressure`). Let $P_n, Q_n$ be pressures, let $a_n > 0$ and $\delta_n \ge 0$ be sequences, and let $U, C \ge 0$, $C_0$ and $k, l > 0$ be constants. Assume, for every $n$:
--   - $P_n$ and $Q_n$ are convex on $\{\beta > 0\}$;
--   - $P_{n+1}$ = `idealAttraction Q n (a n)`;
--   - on `phaseWindow (1/4)`: $|Q_n - P_n| \le \delta_n$, $P_n$ is $C$-Lipschitz, and $|P_{n+1} - Q_n| \le C_0 a_n$;
--   - every ideal attraction supremum for $Q_n$ with mass $a_n$ is attained (`hact`), with a maximizing shift in $[0, U]$ on `phaseWindow (1/2)` (`hcut`).
--
--   Assume the initial condition `hinit`: on `phaseWindow (1/4)`, $P_0$ has three phase groups of radius `phaseRadius/2` and is within `pressureRadius/64` of `threePlane`. Assume also the four budget conditions `hdom`, `hrad`, `hband` and `hpress` on the partial sums of $a_j$ and $\delta_j$, exactly as in the Lean statement. Then for every $n$ there is a point $x$ within $1/8$ of `phaseCenter` such that every slope within `pressureRadius` of `targetSlope` supports $P_n$ at $x$ over $\{\beta > 0\}$:
--
--   `Metric.closedBall targetSlope pressureRadius ⊆ supportSet (onParameters (P n)) positiveParameters x`.
--
--   The named functions come from the definitions bundle `OAIQWRTD000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.RadialTransition.multiscale_pressure_balls`, OpenAI's lemma of that name in `lean/OAI/Probability/RadialTransition/MultiScale.lean`.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/MultiScale.lean (declaration OAI.RadialTransition.multiscale_pressure_balls)

import Mathlib
import Definitions.Def_OAIQWRTD000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma multiscale_pressure_balls {P Q : ℕ → Pressure} {a δ : ℕ → ℝ} {U C C₀ k l : ℝ}
    (ha : ∀ n, 0 < a n) (hδ : ∀ n, 0 ≤ δ n) (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hk : 0 < k) (hl : 0 < l)
    (hP : ∀ n, ConvexOn ℝ positiveParameters (onParameters (P n)))
    (hQ : ∀ n, ConvexOn ℝ positiveParameters (onParameters (Q n)))
    (hnext : ∀ n, P (n+1)=idealAttraction (Q n) (a n))
    (happ : ∀ n x, x ∈ phaseWindow (1/4) → |onParameters (Q n) x-onParameters (P n) x| ≤ δ n)
    (hlip : ∀ n x, x ∈ phaseWindow (1/4) → ∀ y ∈ phaseWindow (1/4),
      |onParameters (P n) x-onParameters (P n) y| ≤ C*dist x y)
    (hinc : ∀ n x, x ∈ phaseWindow (1/4) → |onParameters (P (n+1)) x-onParameters (Q n) x| ≤ C₀*a n)
    (hact : ∀ n β h, 0 < β → ∃ u, ActiveShift (Q n) (a n) β h u)
    (hcut : ∀ n x, x ∈ phaseWindow (1/2) → ∃ u ∈ Icc (0:ℝ) U, ActiveShift (Q n) (a n) (x 0) (x 1) u)
    (hinit : ∀ x ∈ phaseWindow (1/4), HasPhaseGroups (P 0) x (phaseRadius/2) ∧
      |onParameters (P 0) x-onParameters threePlane x| ≤ pressureRadius/64)
    (hdom : ∀ n, (5/4*U+k+l+1)*(∑ j ∈ Finset.range n, a j) ≤ 1/8)
    (hrad : ∀ n, ∑ j ∈ Finset.range n, (2*δ j/(l*a j)+a j*U^2/2) ≤ phaseRadius/2)
    (hband : ∀ n, 2*(k+2*δ n/(k*a n)+2*C*l/k+phaseRadius)<packingDensity)
    (hpress : ∀ n, ∑ j ∈ Finset.range n, (δ j+C₀*a j) ≤ pressureRadius/64) :
    ∀ n, ∃ x ∈ Metric.ball phaseCenter (1/8),
      Metric.closedBall targetSlope pressureRadius ⊆ supportSet (onParameters (P n)) positiveParameters x := by
  sorry

end RadialTransition
end

end OAI
end
