-- Prove2me | Theorems.Thm_LindleyQueue_Stability_limit_exists
-- name    : LindleyQueue.Stability.limit_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:34:17.090013+00:00
-- url     : https://prove2.me/theorems/8a71e312-1692-45c6-a469-441527494a8b
-- title:
--   Limit display, p. 280 — $\lim_{r\to\infty} F_{r+1}(x) = p(U_s \le x \text{ for all } s \ge 1)$
-- statement:
--   In Lindley's single-server queue (Assumptions 1–2), let $F_r(x) = p(w_r \le x)$ be the waiting-time distribution function of the $r$th customer and let
--
--   $$
--   F(x) = \begin{cases} p(U_s \le x \text{ for all } s \ge 1) & x \ge 0,\\ 0 & x < 0,\end{cases}
--   $$
--
--   where $U_s = u_1 + \dots + u_s$. Then for every real $x$,
--
--   $$
--   \lim_{r \to \infty} F_r(x) = F(x).
--   $$
--
--   For $x \ge 0$ this is the paper's "$\lim_{r\to\infty} F_{r+1}(x) = \lim_{r\to\infty} p(E_r) = p(E)$": the events $E_r = \{U_s \le x \text{ for all } s \le r\}$ decrease to $E = \{U_s \le x \text{ for all } s \ge 1\}$. The limit always exists; whether it is a proper distribution function is the subject of the stability theorem.
--
--   **Formalization Note** For $x < 0$ the limit is $0$, because waiting times are nonnegative; the paper's $F(x) = 0$ for $x < 0$ (p. 280) is built into `Flim`. Lean's `F r` is the paper's $F_{r+1}$, which does not affect the limit.
-- source:
--   Lindley (Proc. Camb. Phil. Soc. 48, 1952), §3, display after eq. (3), p. 280

import Mathlib
import Definitions.Def_LindleyQueue_Stability_Model
open MeasureTheory ProbabilityTheory Filter Topology

namespace LindleyQueue.Stability

/-- The limit display after (3), p. 280: `F_r(x)` converges, as `r → ∞`, to
`F(x) = p(U_s ≤ x for all s ≥ 1)` for `x ≥ 0`, and to `F(x) = 0` for `x < 0`. -/
theorem limit_exists {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (Q : Input Ω P) (x : ℝ) :
    Tendsto (fun r => Q.F r x) atTop (𝓝 (Q.Flim x)) := by sorry

end LindleyQueue.Stability
