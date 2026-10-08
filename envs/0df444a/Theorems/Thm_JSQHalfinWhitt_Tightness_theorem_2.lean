-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_theorem_2
-- name    : JSQHalfinWhitt.Tightness.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:49.430548+00:00
-- url     : https://prove2.me/theorems/01cfabe1-de37-481c-81df-094c492cd3b9
-- title:
--   Theorem 2 — $\mathbb E|\sqrt nX_i| \le C(\beta)$ for $i = 1, 2$ and $\mathbb E|nX_i| \le C(\beta)$ for $i \ge 3$
-- statement:
--   Consider the join-the-shortest-queue system with $n$ identical exponential servers, Poisson arrivals of rate $n\lambda$ and the Halfin–Whitt scaling $\lambda = 1 - \beta/\sqrt n$, $\beta > 0$. Let $Q = (Q_1, Q_2, \dots)$ have a stationary distribution of the chain, $Q_i$ being the number of servers with at least $i$ customers, and set $X_1 = (Q_1 - n)/n$ and $X_i = Q_i/n$ for $i \ge 2$.
--
--   For each $\beta > 0$ there exists a constant $C(\beta)$ such that for all $n \ge 1$ (with $\beta < \sqrt n$) and every stationary distribution of the chain,
--   $$\mathbb E\big|\sqrt n X_i\big| \le C(\beta),\quad i = 1, 2, \tag{2.2}$$
--   $$\mathbb E\big|n X_i\big| \le C(\beta),\quad i \ge 3. \tag{2.3}$$
--
--   The theorem says that, uniformly in the number of servers, the stationary number of idle servers and of servers with at least two customers are $O(\sqrt n)$ on average, and the stationary number of servers with at least $i \ge 3$ customers is $O(1)$ on average. It gives tightness of the diffusion-scaled stationary distributions $\{\sqrt n X\}_n$, one of the two ingredients for the convergence of stationary distributions to the diffusion limit (Proposition 1).
--
--   **Formalization Note** The printed display of Theorem 2 omits the expectation ($|\sqrt n X_i| \le C(\beta)$ and $|nX_i| \le C(\beta)$); read as almost-sure bounds these are false, since $X_2 = 1$ with positive stationary probability. The intended statement, proved in the paper, bounds expectations: (1.3) on p. 2 states $\mathbb E Q_2 \le C(\beta)\sqrt n$ and $\mathbb E Q_i \le C(\beta)$, p. 7 computes $\sqrt n\mathbb E|X_1| = \beta$, p. 10 bounds $\mathbb E\sqrt n X_2$, and App. A.4 (p. 22) opens with "Our goal is to prove (2.3), or that $\mathbb E nX_i = \mathbb E Q_i \le C(\beta)$". That version is stated. The model needs $\lambda > 0$, i.e. $\beta < \sqrt n$; for $n \le \beta^2$ there is no model. The constant $C$ is chosen after $\beta$ and before $n$, $\pi$ and $i$. The stationary distribution is a probability $\pi$ on $S$ with global balance $\pi G_Q = 0$, which for this bounded-rate chain characterizes stationarity; expectations are sums against $\pi$ of bounded functions ($0 \le Q_i \le n$), so they always converge. Lean indices are 0-based: `q.1 0` is $Q_1$, `q.1 1` is $Q_2$, and `q.1 i` with $i \ge 2$ is $Q_{i+1}$, so (2.3) is the Lean range $i \ge 2$.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 5, Theorem 2, (2.2)–(2.3) (expectation form: p. 2 (1.3), p. 7, p. 10, p. 22 App. A.4)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_JSQHalfinWhitt_Tightness_Model

namespace JSQHalfinWhitt.Tightness

/-- Theorem 2 (Braverman, p. 5), with the expectation that the printed display omits: for each
`β > 0` there is a constant `C(β)` such that for every `n ≥ 1` with `β < √n` (so that
`λ = 1 − β/√n > 0`) and every stationary distribution `π` of the `n`-server JSQ chain with
`λ = 1 − β/√n`, `E|√n X_i| ≤ C(β)` for `i = 1, 2` (2.2) and `E|n X_i| ≤ C(β)` for `i ≥ 3` (2.3),
where `X_1 = (Q_1 − n)/n` and `X_i = Q_i/n` for `i ≥ 2`. Lean indices are 0-based: `q.1 0` is
`Q_1`, `q.1 1` is `Q_2`, and `q.1 i` with `i ≥ 2` is `Q_{i+1}`. -/
theorem theorem_2 (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → β < Real.sqrt n →
      ∀ π : State n → ℝ, IsStationaryDist (genQ n (lamHW β n)) π →
        (expect π (fun q => |Real.sqrt n * (((q.1 0 : ℝ) - n) / n)|) ≤ C ∧
          expect π (fun q => |Real.sqrt n * ((q.1 1 : ℝ) / n)|) ≤ C) ∧
        ∀ i : ℕ, 2 ≤ i → expect π (fun q => |(n : ℝ) * ((q.1 i : ℝ) / n)|) ≤ C := by sorry

end JSQHalfinWhitt.Tightness
