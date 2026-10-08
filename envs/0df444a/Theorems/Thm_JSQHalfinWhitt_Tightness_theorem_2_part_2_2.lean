-- Prove2me | Theorems.Thm_JSQHalfinWhitt_Tightness_theorem_2_part_2_2
-- name    : JSQHalfinWhitt.Tightness.theorem_2_part_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:44:57.322706+00:00
-- url     : https://prove2.me/theorems/c8fe368d-a6ed-4930-a4b6-afe46c376286
-- title:
--   Theorem 2, (2.2) — $\mathbb E|\sqrt nX_i| \le C(\beta)$ for $i = 1, 2$
-- statement:
--   For $\beta > 0$ consider the join-the-shortest-queue chain with $n$ servers in the Halfin–Whitt regime $\lambda = 1 - \beta/\sqrt n$, and let $X_1 = (Q_1 - n)/n$ and $X_2 = Q_2/n$ be the fluid-scaled coordinates of a stationary state $Q$. For each $\beta > 0$ there is a constant $C(\beta)$ such that for all $n \ge 1$ with $\beta < \sqrt n$ and every stationary distribution of the chain,
--   $$\mathbb E\big|\sqrt n X_i\big| \le C(\beta),\qquad i = 1, 2. \tag{2.2}$$
--
--   This is the tightness of the diffusion-scaled pair $(\sqrt n X_1, \sqrt n X_2)$ in steady state: the number of idle servers and the number of servers with two or more customers are both of order $\sqrt n$ on average.
--
--   **Formalization Note** The printed display of Theorem 2 omits the expectation and reads $|\sqrt n X_i| \le C(\beta)$; read as an almost-sure bound it is false, since $X_2 = 1$ with positive stationary probability. The intended statement, proved in the paper, is the bound on $\mathbb E|\sqrt n X_i|$: (1.3) on p. 2 states $\mathbb E Q_2 \le C(\beta)\sqrt n$, p. 7 computes $\sqrt n\mathbb E|X_1| = \beta$, and p. 10 bounds $\mathbb E\sqrt n X_2$. That version is stated. The model needs $\lambda > 0$, i.e. $\beta < \sqrt n$; for $n \le \beta^2$ there is no model, so "for all $n \ge 1$" is read as "for all $n \ge 1$ with $\beta < \sqrt n$". The constant $C$ is chosen after $\beta$ and before $n$ and $\pi$.
-- source:
--   Braverman, Steady-State Analysis of the Join-the-Shortest-Queue Model in the Halfin-Whitt Regime, arXiv:1801.05121v2 (published in Math. Oper. Res. 45(3), 2020), p. 5, Theorem 2, (2.2) (expectation form: p. 2 (1.3), p. 7, p. 10)

import Mathlib
import Definitions.Def_JSQHalfinWhitt_Tightness_Stationary
import Definitions.Def_JSQHalfinWhitt_Tightness_Model

namespace JSQHalfinWhitt.Tightness

/-- Theorem 2, (2.2) (Braverman, p. 5), with the expectation that the printed display omits:
for each `β > 0` there is `C(β)` such that for every `n ≥ 1` with `β < √n` and every stationary
distribution `π` of the JSQ chain with `λ = 1 − β/√n`, `E|√n X_1| ≤ C(β)` and `E|√n X_2| ≤ C(β)`,
where `X_1 = (Q_1 − n)/n`, `X_2 = Q_2/n` (Lean `q.1 0`, `q.1 1`). -/
theorem theorem_2_part_2_2 (β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → β < Real.sqrt n →
      ∀ π : State n → ℝ, IsStationaryDist (genQ n (lamHW β n)) π →
        expect π (fun q => |Real.sqrt n * (((q.1 0 : ℝ) - n) / n)|) ≤ C ∧
          expect π (fun q => |Real.sqrt n * ((q.1 1 : ℝ) / n)|) ≤ C := by sorry

end JSQHalfinWhitt.Tightness
