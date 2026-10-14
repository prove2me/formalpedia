-- Prove2me | Theorems.Thm_GreedyRS_Tight_ec1_8_pics_event
-- name    : GreedyRS.Tight.ec1_8_pics_event
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:36.251984+00:00
-- url     : https://prove2.me/theorems/f9f62a63-3ffc-404b-821f-d44a40c71e68
-- title:
--   (EC.1.8), p. ec4 — PICS ≥ Pr{Σ N_i(min_{n≤m_ϵ−1} X̄₁(n)) + m_ϵ ≤ B < Σ N_i(min_{n≤m_ϵ} X̄₁(n)) + m_ϵ}
-- statement:
--   Let $X_{ij}$ be a normal array (independent observations $X_{ij} \sim N(\mu_i, \sigma_i^2)$) with every variance $\sigma_i^2 > 0$, and run the greedy procedure on alternatives $1, \dots, k$ with total budget $B$. Fix a level $\gamma^+ \in \mathbb R$ and let
--   $$m = \inf\{n \ge 1 : \bar X_1(n) < \mu_1 - \gamma^+\}$$
--   be the first time the running average of the best alternative drops below $\mu_1 - \gamma^+$. For $i \ge 2$ write $N_i(\min_{1\le n\le m'} \bar X_1(n)) = \inf\{n \ge 1 : \bar X_i(n) < \bar X_1(j) \text{ for all } 1 \le j \le m'\}$, with the convention that this is $1$ when $m' = 0$ (i.e. $\bar X_1(0) = \infty$). Then the probability of incorrect selection satisfies
--   $$\mathrm{PICS} \ge \Pr\Big\{ m < \infty,\ \sum_{i=2}^k N_i\Big(\min_{1\le n\le m-1} \bar X_1(n)\Big) + m \le B < \sum_{i=2}^k N_i\Big(\min_{1\le n\le m} \bar X_1(n)\Big) + m \Big\}.$$
--
--   In words: once the best alternative's running average has dropped below the level, if the budget sufficed to bring it to that point but does not suffice to push every competitor below its new minimum, the greedy procedure ends with a wrong selection. This is the starting inequality of the upper half of Theorem 2.
--
--   **Formalization Note.** The paper states (EC.1.8) under the slippage configuration, with $\gamma^+ = \gamma_\epsilon^+$ from (EC.1.7) and on the event $B_\epsilon$; the inequality itself uses none of these, so the Lean statement holds for every level $\gamma^+$, every means and every positive variances (positive variances make the ties $\bar X_i(n) = \bar X_1(m)$ null events). Alternatives are 0-based in Lean (the paper's alternative $i$ is Lean's $i-1$), sums of crossing times are in $\mathbb N \cup \{\infty\}$, and $m - 1$ is natural-number subtraction, which is exact since $m \ge 1$.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. ec4 (PDF 43), EC.1.4, Equation (EC.1.8)

import Mathlib
import Definitions.Def_GreedyRS_Tight_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GreedyRS.Tight

theorem ec1_8_pics_event {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : GreedyRS.Greedy.NormalArray P μ v X)
    (hv : ∀ i, 0 < v i) (k B : ℕ) (γp : ℝ) :
    P {ω | ∃ m : ℕ, GreedyRS.Greedy.crossBelow (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) (μ 0 - γp) 1 = m ∧
        (∑ i ∈ Finset.Ico 1 k, prefixCross (GreedyRS.Greedy.runMean (fun i j => X i j ω) i)
            (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) (m - 1)) + m ≤ B ∧
        (B : ℕ∞) < (∑ i ∈ Finset.Ico 1 k, prefixCross (GreedyRS.Greedy.runMean (fun i j => X i j ω) i)
            (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) m) + m}
      ≤ P {ω | GreedyRS.Greedy.greedySelect k B (fun i j => X i j ω) ≠ 0} := by sorry

end GreedyRS.Tight
