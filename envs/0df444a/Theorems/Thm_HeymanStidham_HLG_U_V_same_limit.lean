-- Prove2me | Theorems.Thm_HeymanStidham_HLG_U_V_same_limit
-- name    : HeymanStidham.HLG.U_V_same_limit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:39:20.134986+00:00
-- url     : https://prove2.me/theorems/fb3c4371-f7ca-41bc-80cd-9000cfbcc9f2
-- title:
--   p. 986 — lim U(t)/t = lim V(t)/t (= λG)
-- statement:
--   Let $0 \le t_1 \le t_2 \le \cdots$ be arrival epochs with $\lim_{t\to\infty} N(t)/t = \lambda$, $0 < \lambda < \infty$. Let $a_n \ge 0$ have finite customer average $G = \lim_{N\to\infty}\frac1N\sum_{n=1}^N a_n$, and let $s_n \ge 0$ with $s_n/t_n \to 0$. With $U(t) = \sum_{n:\, t_n \le t} a_n$ and $V(t) = \sum_{n:\, t_n + s_n \le t} a_n$,
--
--   $$
--   \lim_{t\to\infty} \frac{V(t)}{t} = \lim_{t\to\infty} \frac{U(t)}{t} = \lambda G .
--   $$
--
--   This is the step that completes the proof of Theorem 1: combined with (3) and (4), it squeezes $\frac1T\int_0^T h$ to $\lambda G$. The page states it as $\lim U(t)/t = \lim V(t)/t$; the value $\lambda G$ of the common limit is (4).
--
--   **Formalization Note** The statement is given for an arbitrary nonnegative sequence $(a_n)$ (the paper's $g_n \ge 0$, by (iii)) and assumes $s_n/t_n \to 0$ directly, as the page does ("using $\lim s_n/t_n = 0$"). $V$ is an infinite sum in Lean; it equals the page's finite sum because $\lambda > 0$ makes $\{n : t_n \le t\}$ finite.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), p. 986, proof of Theorem 1, first paragraph (by mimicking Theorem 2 of Stidham 1974)

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace HeymanStidham.HLG

/-- p. 986: with `aₙ ≥ 0`, `sₙ ≥ 0`, `sₙ/tₙ → 0`, `0 < λ < ∞` and customer average `G`,
`V(t)/t` has the same limit `λG` as `U(t)/t`, where `V(t) = Σ_{tₙ + sₙ ≤ t} aₙ`. -/
theorem U_V_same_limit (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n) (hst : Tendsto (fun n : ℕ => s n / t n) atTop (𝓝 0))
    (lam : ℝ) (hlam : 0 < lam) (hrate : IsArrivalRate t lam)
    (G : ℝ) (hG : IsCustomerAverage a G) :
    Tendsto (fun T : ℝ => finishedTotal t s a T / T) atTop (𝓝 (lam * G)) := by sorry

end HeymanStidham.HLG
