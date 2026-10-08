-- Prove2me | Theorems.Thm_HeymanStidham_HLG_s_div_t_tendsto_zero
-- name    : HeymanStidham.HLG.s_div_t_tendsto_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:35:32.668315+00:00
-- url     : https://prove2.me/theorems/520b3922-6f48-47b1-9a8b-51871b50c59b
-- title:
--   p. 986 — lim sₙ/tₙ = 0, from (ii), (2) and λ < ∞
-- statement:
--   Let $0 \le t_1 \le t_2 \le \cdots$ be arrival epochs with $\lim_{t\to\infty} N(t)/t = \lambda$, $0 < \lambda < \infty$, and let $(s_n)$ satisfy assumption (ii), $s_n/n \to 0$. Then
--
--   $$
--   \lim_{n\to\infty} \frac{s_n}{t_n} = 0.
--   $$
--
--   The proof of Theorem 1 states that this follows from (ii), (2) and $\lambda < \infty$, and uses it to show that $U(t)/t$ and $V(t)/t$ have the same limit.
--
--   **Formalization Note** Customers are 0-based in Lean, so (ii) reads $s_n/(n+1) \to 0$. Since $t_n \to \infty$ by (2), $t_n > 0$ for all large $n$, and the finitely many quotients with $t_n = 0$ do not affect the limit.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), p. 986, proof of Theorem 1, first paragraph

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace HeymanStidham.HLG

/-- p. 986: (ii) together with (2) and `0 < λ < ∞` gives `sₙ/tₙ → 0`. -/
theorem s_div_t_tendsto_zero (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (s : ℕ → ℝ) (hII : CondII s)
    (lam : ℝ) (hlam : 0 < lam) (hrate : IsArrivalRate t lam) :
    Tendsto (fun n : ℕ => s n / t n) atTop (𝓝 0) := by sorry

end HeymanStidham.HLG
