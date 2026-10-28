-- Prove2me | Theorems.Thm_FragLOB_Collapse_eq_12
-- name    : FragLOB.Collapse.eq_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:48.138692+00:00
-- url     : https://prove2.me/theorems/f63e035a-1893-4034-b8a1-4441c7ee6b15
-- title:
--   (12), §3.2, p. 1331 — the expected delay on every exchange is W/(μβ_i)
-- statement:
--   Consider the fragmented limit order book market with $N$ exchanges, market-order rate $\mu > 0$ and attraction coefficients $\beta_i > 0$. Let $Q \in \mathbb R^N_+$ be a vector of queue lengths with positive workload $W = \sum_{i=1}^N \beta_i Q_i > 0$, and let the market orders be split by the linear attraction model $\mu_i(Q) = \mu\beta_i Q_i/W$. Then the expected delay on every exchange $i$ is
--
--   $$\mathrm{ED}_i = \frac{W}{\mu\beta_i}.$$
--
--   So the one-dimensional workload determines the delays at all exchanges at once. This is the identity (12) of the paper and the first ingredient of state space collapse.
--
--   **Formalization Note.** For $Q_i > 0$ the delay is defined by (1) as $Q_i/\mu_i(Q)$, and the statement is the identity $Q_i/\mu_i(Q) = W/(\mu\beta_i)$. At an empty exchange ($Q_i = 0$), where (1) reads $0/0$, the delay is defined as $W/(\mu\beta_i)$, so the claim there holds by that convention.
-- source:
--   Maglaras, Moallemi & Zheng, Operations Research 69(4):1324–1348 (2021), p. 1331, §3.2, eq. (12)

import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory

namespace FragLOB.Collapse

theorem eq_12 {N : ℕ} (M : Market N) (hM : M.Standing) (Q : Fin N → ℝ)
    (hQ : ∀ i, 0 ≤ Q i) (hW : 0 < workload M Q) :
    ∀ i, delay M Q i = workload M Q / (M.mu * M.beta i) := by sorry

end FragLOB.Collapse
