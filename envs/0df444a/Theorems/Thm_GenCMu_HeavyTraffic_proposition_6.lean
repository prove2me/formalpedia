-- Prove2me | Theorems.Thm_GenCMu_HeavyTraffic_proposition_6
-- name    : GenCMu.HeavyTraffic.proposition_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:04.804765+00:00
-- url     : https://prove2.me/theorems/c9a8dada-435f-494d-b97a-926cc216a0c3
-- title:
--   Proposition 6 — the asymptotic cost of any feasible policy is bounded below: $\liminf_n\tilde J^n(t)\ge\tilde J^*(t)$
-- statement:
--   Let $(Q^n)$ be a heavy-traffic sequence satisfying Assumptions 1 and 2 and let $T^n$ be cost-admissible policies, including policies that idle while work waits. Then for each $t \in [0,1]$
--   $$\liminf_{n\to\infty}\tilde J^n(t) \ge \tilde J^*(t) \qquad (44),$$
--   where
--   $$\tilde J^*(t) = \sum_k\int_0^t \lambda_k(s)\,C^*_k\Big(\frac{[g\circ\tilde W^*_+]_k(s)}{\rho_k(s)}\Big)\,ds \qquad (45),$$
--   $g\circ\tilde W^*_+(s)$ being a solution of (43) at $y = \tilde W^*_+(s)$.
--
--   No sequence of work-conserving policies, converging or not, does better asymptotically than splitting the limit total workload optimally at every instant. Proposition 7 shows the bound is attained.
--
--   **Formalization Note** The integrand of (45) is the optimal value of (43) at $\tilde W^*_+(s)$ for any minimizer, and $\tilde J^*$ is defined as the integral of that value, so no choice of $g$ or uniqueness of minimizers is needed. $\liminf_n \tilde J^n(t)\ge\tilde J^*(t)$ is stated as: for every $\varepsilon > 0$, eventually $\tilde J^n(t) \ge \tilde J^*(t) - \varepsilon$. The paper states it "for any sequence of feasible policies"; the policies are feasible and work conserving as in `GenCMu.HeavyTraffic.Model`.
--
--   **Formalization Note** `IsCostAdmissible` includes the paper's F1 initial condition and F2–F4, plus nonnegative workload and finite delays so that the cost in (3) is defined by actual completion times. It does not impose work conservation.
-- source:
--   Van Mieghem, Dynamic Scheduling with Convex Delay Costs: The Generalized cμ Rule, Ann. Appl. Probab. 5(3) (1995), §4.1, p. 820, Proposition 6, (44)–(45)

import Mathlib
import Definitions.Def_GenCMu_HeavyTraffic_Model
import Definitions.Def_GenCMu_HeavyTraffic_Sequence
import Definitions.Def_GenCMu_HeavyTraffic_Limits

namespace GenCMu.HeavyTraffic

open Filter Topology Finset


/-- Proposition 6 (p. 820): under Assumptions 1 and 2, every admissible policy sequence,
including policies that idle with work waiting, obeys the lower bound at each `t ∈ [0,1]`. -/
theorem proposition_6 {d : ℕ} (H : HTSeq d) (M : Limits d) (h1 : MainConvergence H M) (Cs : Fin d → ℝ → ℝ) (h2 : CostConvergence H Cs) (T : ℕ → Alloc d) (hT : ∀ n, (H.Q n).IsCostAdmissible (T n)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Jstar M Cs t - ε ≤ H.Jt T n t := by sorry
end GenCMu.HeavyTraffic
