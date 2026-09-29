-- Prove2me | Theorems.Thm_GravesWillems_Serial_binding_base_stocks_optimal
-- name    : GravesWillems.Serial.binding_base_stocks_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:21:20.399543+00:00
-- url     : https://prove2.me/theorems/80431763-f0ad-4945-b904-a7c4e2f4056a
-- title:
--   Appendix, Result (Eq. (A6)) — the binding base stocks are optimal for $\mathbf P^*$
-- statement:
--   Consider a serial supply chain with $N$ stages, stage $1$ the demand node and stage $i$ supplying stage $i-1$, with deterministic lead times $T_1, \dots, T_N \in \mathbb{N}$, holding costs $h_1, \dots, h_N$, and a random end-item demand path $d$ on a probability space $(\Omega, \mu)$ whose demand in every period is integrable. Let $D : \mathbb{N} \to \mathbb{R}$ be the demand bound ($D(\tau)$ the maximum end-item demand over $\tau$ periods). Program $\mathbf P^*$ is
--   $$\min_B\ \sum_{i=1}^N h_i B_i - \sum_{i=2}^N e_{i-1} E[Q_i] \quad \text{s.t.}\quad B_1 + \dots + B_i \ge D(T_1 + \dots + T_i),\ B_i \ge 0\ (i = 1, \dots, N),$$
--   with echelon holding costs $e_i = h_i - h_{i+1}$ and $Q_i$ the backlog of the recursion (A1).
--
--   **Result.** If the echelon holding costs are nonnegative and $D$ is nondecreasing (with $D(0) = 0$), then an optimal solution to $\mathbf P^*$ is given by
--   $$B_1 = D(T_1), \qquad B_i = D(T_1 + \dots + T_i) - D(T_1 + \dots + T_{i-1}), \quad i = 2, \dots, N. \tag{A6}$$
--   Precisely: (A6) is feasible, and for every period $t$ its objective value is at most that of every feasible base-stock vector.
--
--   The optimal base stocks do not depend on the holding costs at all: they cover exactly the incremental maximal demand over each stage's lead time. The result quantifies the cost of the guaranteed-service assumption used in the body of the paper.
--
--   **Formalization Note** Two readings of the page are made explicit. (1) "The echelon holding costs are nonnegative" is read as $e_i = h_i - h_{i+1} \ge 0$ for $1 \le i < N$ and $e_N = h_N \ge 0$ (i.e. $h_{N+1} := 0$); the proof's case $k = N$ uses $h_N \ge 0$, and without it the Result fails ($N = 1$, $h_1 < 0$). (2) $D(0) = 0$, the paper's convention (§2, p. 70, "We define $D_j(0) = 0$"); without it (A6) can be infeasible ($D \equiv -1$). The paper writes $E[Q_i]$ for a stationary demand process; here the objective is taken at a fixed period $t$ and the statement holds for every $t$, with no stationarity assumed. The demand bound $d(a, a+s] \le D(s)$ is not a hypothesis: the Result does not use it.
-- source:
--   Graves and Willems, Optimizing Strategic Safety Stock Placement in Supply Chains, Manufacturing & Service Operations Management 2(1), 2000, p. 81, Appendix, Result, Eq. (A6); proof pp. 81-82

import Mathlib
import Definitions.Def_GravesWillems_Serial_backlog
import Definitions.Def_GravesWillems_Serial_programP
open MeasureTheory

namespace GravesWillems.Serial

/-- The Result of the Appendix of Graves–Willems 2000 (p. 81, Eq. (A6)): if the echelon holding
costs are nonnegative (`hᵢ − h_{i+1} ≥ 0` for `1 ≤ i < N`, and `h_N ≥ 0`, i.e. `e_N ≥ 0` with
`h_{N+1} = 0`) and the demand bound `D` is nondecreasing with `D(0) = 0`, then the vector (A6)
is an optimal solution of program `P*`: it is feasible, and at every period `t` its objective
value is at most that of every feasible base-stock vector. -/
theorem binding_base_stocks_optimal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : Ω → ℤ → ℝ) (hd : ∀ τ : ℤ, Integrable (fun ω => d ω τ) μ)
    (N : ℕ) (T : ℕ → ℕ) (D : ℕ → ℝ) (hD0 : D 0 = 0) (hD : Monotone D)
    (h : ℕ → ℝ) (he : ∀ i ∈ Finset.Ico 1 N, 0 ≤ h i - h (i + 1)) (hhN : 0 ≤ h N) (t : ℤ) :
    Feasible N T D (a6 N T D) ∧
    ∀ B : ℕ → ℝ, Feasible N T D B →
      objective μ d N T h (a6 N T D) t ≤ objective μ d N T h B t := by sorry

end GravesWillems.Serial
