-- Prove2me | Theorems.Thm_MDPComplexity_AverageCost_theorem3_min_mean_cycle
-- name    : MDPComplexity.AverageCost.theorem3_min_mean_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:58:25.295212+00:00
-- url     : https://prove2.me/theorems/4245cfe0-f6e9-4160-94dd-55e58ec2c1e6
-- title:
--   Optimal deterministic average cost equals the least reachable cycle mean
-- statement:
--   Let $M$ be a finite stationary deterministic Markov decision process with initial state $s_0$, and let $n=|S|$. Policies choose a decision for every state and time. The optimal upper-limit average cost is the least mean cost of a reachable simple cycle. A policy attains this value with genuinely convergent finite averages. The same value is obtained from the min-plus adjacency matrix $A$:
--
--   $$g^*(s_0)=\min_{\substack{C\text{ simple cycle}\\C\text{ reachable from }s_0}}\operatorname{mean}(C)=\min_{\substack{u\text{ reachable from }s_0\\1\leq k\leq n\\(A^k)_{uu}<+\infty}}\frac{(A^k)_{uu}}{k}.$$
--
--   This is the mathematical identity behind the paper's parallel algorithm for deterministic average cost.
--
--   **Formalization Note** The paper's Theorem 3 asserts membership in NC; this item formalizes the exact optimization identity used there, not the complexity bound. The paper writes a limit for arbitrary policies, although a time-dependent policy's averages may oscillate; the optimum here uses limsup, and the least-cost policy has a genuine limit. The formula excludes unreachable cycles and infinite matrix entries. The printed $T+1$ terms divided by $T$ are retained, with the $T=0$ value irrelevant to the limit.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 446, §3 The infinite horizon undiscounted case and Theorem 3, https://doi.org/10.1287/moor.12.3.441

import Definitions.Def_MDPComplexity_AverageCost_Model

namespace MDPComplexity.AverageCost

open Filter

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- The identity underlying Theorem 3 (p. 446). The optimum over all
time-dependent policies is the least reachable simple-cycle mean, is attained
as a limit, and equals the min-plus calculation over closed walks of length at most n. -/
theorem theorem3_min_mean_cycle (M : DetMDP S) (s₀ : S) :
    IsLeast {μ : ℝ | ∃ C : M.Cycle,
      M.Reachable s₀ C.base ∧ μ = C.mean} (M.optAvg s₀) ∧
    (∃ δ : M.Policy, Tendsto (M.average s₀ δ) atTop (nhds (M.optAvg s₀))) ∧
    IsLeast {μ : ℝ | ∃ (u : S) (k : ℕ) (r : ℝ),
      M.Reachable s₀ u ∧ 1 ≤ k ∧ k ≤ Fintype.card S ∧
      M.minPlusPow k u u = (r : WithTop ℝ) ∧ μ = r / k} (M.optAvg s₀) := by sorry

end MDPComplexity.AverageCost
