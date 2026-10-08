-- Prove2me | Theorems.Thm_HeymanStidham_HLG_theorem_1
-- name    : HeymanStidham.HLG.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:39:22.640115+00:00
-- url     : https://prove2.me/theorems/2ea95a8e-d407-4044-a5ab-abea216d2081
-- title:
--   THEOREM 1, p. 985 — for fₙ ≥ 0 under (i)–(iv), H = λG
-- statement:
--   Let $0 \le t_1 \le t_2 \le \cdots$ be the arrival epochs of customers $1, 2, \ldots$ and $N(t)$ the number of $n$ with $t_n \le t$. Customer $n$ carries a function $f_n$ on $[0,\infty)$; let $g_n = \int_0^\infty f_n(t)\,dt$ and $h(t) = \sum_{n=1}^\infty f_n(t)$. Assume that for each $n$ there is $s_n \in [0,\infty)$ such that
--
--   1. (i) $f_n(t) = 0$ for $t \notin [t_n, t_n + s_n]$;
--   2. (ii) $s_n/n \to 0$;
--   3. (iii) $f_n(t) \ge 0$;
--   4. (iv) $\int_0^\infty f_n(t)\,dt < \infty$.
--
--   If $\lambda = \lim_{t\to\infty} N(t)/t$ and $G = \lim_{N\to\infty} \frac1N\sum_{n=1}^N g_n$ exist with $0 < \lambda < \infty$ and $G < \infty$, then $H = \lim_{T\to\infty} \frac1T\int_0^T h(t)\,dt$ exists and
--
--   $$
--   H = \lambda G. \tag{1}
--   $$
--
--   This is the nonnegative case of the relation $H = \lambda G$ between time and customer averages. With $f_n$ the indicator of customer $n$'s sojourn it is Little's law $L = \lambda W$, and the proof of Theorem 2 applies it to $f_n^+$ and $f_n^-$.
--
--   **Formalization Note** Customers are 0-based in Lean, so (ii) reads $s_n/(n+1) \to 0$. Ties between arrival epochs are allowed. The page prints (iv) as "$\int_0^\infty f_n\,dt \le \infty$", a misprint for "$< \infty$"; Lean states (iv) as integrability of $f_n$ on $[0,\infty)$, which also carries the measurability the page presupposes ("assume that these functions are well defined"). The conclusion "$H$ exists" includes that $h$ is integrable on every $[0,T]$. $N(t)$ is the cardinality of $\{n : t_n \le t\}$, which is finite because $\lambda > 0$.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), p. 985, THEOREM 1 and display (1)

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace HeymanStidham.HLG

/-- THEOREM 1, p. 985: under (i), (ii), (iii) `fₙ ≥ 0` and (iv) `∫₀^∞ fₙ < ∞`, if
`λ` and `G` exist with `0 < λ < ∞` and `G < ∞`, then `H` exists and `H = λG` (1). -/
theorem theorem_1 (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (f : ℕ → ℝ → ℝ) (s : ℕ → ℝ) (hI : CondI t f s) (hII : CondII s)
    (lam : ℝ) (hlam : 0 < lam) (hrate : IsArrivalRate t lam)
    (hiii : ∀ n τ, 0 ≤ τ → 0 ≤ f n τ)
    (hiv : ∀ n, IntegrableOn (f n) (Set.Ici 0))
    (G : ℝ) (hG : IsCustomerAverage (custTotal f) G) :
    IsTimeAverage (rate f) (lam * G) := by sorry

end HeymanStidham.HLG
