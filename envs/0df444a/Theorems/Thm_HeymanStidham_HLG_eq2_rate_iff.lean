-- Prove2me | Theorems.Thm_HeymanStidham_HLG_eq2_rate_iff
-- name    : HeymanStidham.HLG.eq2_rate_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:33:36.934185+00:00
-- url     : https://prove2.me/theorems/57793e19-2d39-4635-950f-9353ef109dcb
-- title:
--   (2), p. 985 — for 0 < λ < ∞, N(t)/t → λ iff tₙ/n → λ⁻¹
-- statement:
--   Let $0 \le t_1 \le t_2 \le \cdots$ be arrival epochs, $N(t)$ the number of $n$ with $t_n \le t$, and $0 < \lambda < \infty$. Then
--
--   $$
--   \lim_{t\to\infty} \frac{N(t)}{t} = \lambda \iff \lim_{n\to\infty} \frac{t_n}{n} = \lambda^{-1}.
--   $$
--
--   This is Lemma 3 of Stidham (1972), quoted as display (2) in the proof of Theorem 1. It converts the arrival rate, a time-indexed limit, into a statement about the arrival epochs, a customer-indexed limit; in particular it shows $t_n < \infty$ for every $n$ and $t_n \to \infty$.
--
--   **Formalization Note** Customers are 0-based in Lean, so $t_n/n$ reads $t_n/(n+1)$. $N(t)$ is the cardinality of $\{n : t_n \le t\}$.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), p. 985, proof of Theorem 1, display (2) (Lemma 3 of Stidham 1972)

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace HeymanStidham.HLG

/-- (2), p. 985 (Lemma 3 of Stidham 1972): for nondecreasing arrival epochs and
`0 < λ < ∞`, `N(t)/t → λ` if and only if `tₙ/n → λ⁻¹`. -/
theorem eq2_rate_iff (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (lam : ℝ) (hlam : 0 < lam) :
    IsArrivalRate t lam ↔ Tendsto (fun n : ℕ => t n / ((n : ℝ) + 1)) atTop (𝓝 lam⁻¹) := by sorry

end HeymanStidham.HLG
