-- Prove2me | Theorems.Thm_HeymanStidham_HLG_eq4_lambda_G
-- name    : HeymanStidham.HLG.eq4_lambda_G
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:35:12.755626+00:00
-- url     : https://prove2.me/theorems/df952258-5e06-4577-b52c-bc63b0f0d6f2
-- title:
--   (4), p. 985 — λG = lim U(t)/t
-- statement:
--   Let $0 \le t_1 \le t_2 \le \cdots$ be arrival epochs with $\lim_{t\to\infty} N(t)/t = \lambda$, where $0 < \lambda < \infty$ and $N(t)$ is the number of $n$ with $t_n \le t$. Let $(a_n)$ be a real sequence whose customer average $G = \lim_{N\to\infty} \frac1N \sum_{n=1}^N a_n$ exists and is finite, and let $U(t) = \sum_{n:\, t_n \le t} a_n$. Then
--
--   $$
--   \lambda G = \lim_{t\to\infty} \frac{N(t)}{t}\cdot\frac{1}{N(t)}\sum_{n=1}^{N(t)} a_n = \lim_{t\to\infty} \frac{U(t)}{t}.
--   $$
--
--   This is display (4) in the proof of Theorem 1, applied there with $a_n = g_n$. It turns the customer average into the long-run rate of the arrived totals.
--
--   **Formalization Note** The statement is given for an arbitrary sequence $(a_n)$, of which the paper's $g_n$ is an instance; the claim does not use any property of $g_n$.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), p. 985, proof of Theorem 1, display (4)

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace HeymanStidham.HLG

/-- (4), p. 985: if `λ = lim N(t)/t` exists with `0 < λ < ∞` and the customer average
`G` of `(aₙ)` exists, then `U(t)/t → λG`, where `U(t) = Σ_{tₙ ≤ t} aₙ`. -/
theorem eq4_lambda_G (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (a : ℕ → ℝ) (lam : ℝ) (hlam : 0 < lam) (hrate : IsArrivalRate t lam)
    (G : ℝ) (hG : IsCustomerAverage a G) :
    Tendsto (fun T : ℝ => arrivedTotal t a T / T) atTop (𝓝 (lam * G)) := by sorry

end HeymanStidham.HLG
