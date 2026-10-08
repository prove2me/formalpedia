-- Prove2me | Theorems.Thm_HeymanStidham_HLG_theorem_2
-- name    : HeymanStidham.HLG.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:39:52.893562+00:00
-- url     : https://prove2.me/theorems/c99c8a4f-897b-4a93-beea-10912796d585
-- title:
--   THEOREM 2, p. 986 — under (i), (ii), (v), 0 < λ < ∞ and finite G⁺, G⁻: G and H exist and H = λG
-- statement:
--   Let $0 \le t_1 \le t_2 \le \cdots$ be the arrival epochs of customers $1, 2, \ldots$, and $N(t)$ the number of $n$ with $t_n \le t$. Customer $n$ carries a real-valued (possibly negative) function $f_n$ on $[0,\infty)$. Write $f_n^+ = \max[0, f_n]$, $f_n^- = \max[0, -f_n]$, $g_n = \int_0^\infty f_n\,dt$, $g_n^\pm = \int_0^\infty f_n^\pm\,dt$ and $h(t) = \sum_{n=1}^\infty f_n(t)$. Assume that for each $n$ there is $s_n \in [0,\infty)$ such that
--
--   1. (i) $f_n(t) = 0$ for $t \notin [t_n, t_n + s_n]$;
--   2. (ii) $s_n/n \to 0$;
--   3. (v) $\int_0^\infty |f_n(t)|\,dt < \infty$.
--
--   If $\lambda = \lim_{t\to\infty} N(t)/t$, $G^+ = \lim_N \frac1N\sum_{n=1}^N g_n^+$ and $G^- = \lim_N \frac1N\sum_{n=1}^N g_n^-$ exist, with $0 < \lambda < \infty$, $G^+ < \infty$ and $G^- < \infty$, then $G = \lim_N \frac1N\sum_{n=1}^N g_n$ exists and equals $G^+ - G^-$, $H = \lim_{T\to\infty} \frac1T\int_0^T h(t)\,dt$ exists, and
--
--   $$
--   H = \lambda G. \tag{1}
--   $$
--
--   This is the main result of the paper: a sample-path relation between the time average of $h$ and the customer average of the $g_n$, valid for signed $f_n$ under the mild support condition (i)–(ii). It contains Theorem 1 ($f_n \ge 0$) and Little's law $L = \lambda W$.
--
--   **Formalization Note** The statement is about one fixed sample path; the paper's "with probability one" is this statement applied to almost every path. Customers are 0-based in Lean, so (ii) reads $s_n/(n+1) \to 0$; ties between arrival epochs are allowed. (v) is integrability of $f_n$ on $[0,\infty)$. The page's (1) speaks of $G$, which the hypotheses do not give directly; its existence and value $G^+ - G^-$ (shown in the proof, display (6)) are the first part of the conclusion. "$H$ exists" includes integrability of $h$ on every $[0,T]$, so a non-integrable $h$ cannot have "time average" $0$. $h$ is the full infinite sum over all customers. $N(t)$ is the cardinality of $\{n : t_n \le t\}$, finite because $\lambda > 0$.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), p. 986, THEOREM 2, with display (1) (p. 985) and (6) (p. 986)

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace HeymanStidham.HLG

/-- THEOREM 2, p. 986: under (i), (ii) and (v) `∫₀^∞ |fₙ| < ∞`, if `λ`, `G⁺`, `G⁻` exist
with `0 < λ < ∞` and `G⁺, G⁻ < ∞`, then `G = G⁺ − G⁻` exists, `H` exists, and
`H = λG` (1). -/
theorem theorem_2 (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (f : ℕ → ℝ → ℝ) (s : ℕ → ℝ) (hI : CondI t f s) (hII : CondII s)
    (lam : ℝ) (hlam : 0 < lam) (hrate : IsArrivalRate t lam)
    (hv : ∀ n, IntegrableOn (f n) (Set.Ici 0))
    (Gp Gm : ℝ)
    (hGp : IsCustomerAverage (custTotal (posPartFn f)) Gp)
    (hGm : IsCustomerAverage (custTotal (negPartFn f)) Gm) :
    IsCustomerAverage (custTotal f) (Gp - Gm) ∧
      IsTimeAverage (rate f) (lam * (Gp - Gm)) := by sorry

end HeymanStidham.HLG
