-- Prove2me | Theorems.Thm_HeymanStidham_HLG_eq3_sandwich
-- name    : HeymanStidham.HLG.eq3_sandwich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:35:00.387256+00:00
-- url     : https://prove2.me/theorems/ea7872fd-5fd9-454c-85a6-abf47d19c2b9
-- title:
--   (3), p. 985 — V(T) ≤ ∫₀ᵀ h(t)dt ≤ U(T) for nonnegative fₙ under (i)
-- statement:
--   Let $0 \le t_1 \le t_2 \le \cdots$ be arrival epochs with $t_n \to \infty$. For each customer $n$ let $f_n$ be a function on $[0,\infty)$ and $s_n \ge 0$ such that
--
--   1. (i) $f_n(t) = 0$ for $t \notin [t_n, t_n + s_n]$;
--   2. (iii) $f_n(t) \ge 0$;
--   3. (iv) $f_n$ is integrable on $[0,\infty)$.
--
--   Let $g_n = \int_0^\infty f_n(t)\,dt$, $h(t) = \sum_n f_n(t)$, $N_1(T) = \{n : t_n \le T\}$, $N_2(T) = \{n : t_n + s_n \le T\}$, $U(T) = \sum_{n\in N_1(T)} g_n$ and $V(T) = \sum_{n\in N_2(T)} g_n$. Then for every $T \ge 0$, $h$ is integrable on $[0,T]$ and
--
--   $$
--   U(T) \ \ge\ \int_0^T h(t)\,dt\ \ge\ V(T).
--   $$
--
--   This is display (3) in the proof of Theorem 1: the time integral of $h$ is squeezed between the totals of the customers that have arrived and of those whose window $[t_n, t_n + s_n]$ has closed.
--
--   **Formalization Note** The hypothesis $t_n \to \infty$ is the page's remark that $N_1(T)$ and $N_2(T)$ are "finite for every finite $T$", which the proof draws from (2); here it is assumed directly. The integrability of $h$ on $[0,T]$ is part of the conclusion. $U$, $V$ and $h$ are infinite sums in Lean, which equal the finite sums of the page under these hypotheses.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), p. 985, proof of Theorem 1, display (3) (by mimicking Lemma 1 of Stidham 1974)

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace HeymanStidham.HLG

/-- (3), p. 985: for nonnegative customer functions satisfying (i) and (iv), with arrival
epochs tending to infinity, `h` is integrable on `[0, T]` and `V(T) ≤ ∫₀^T h ≤ U(T)`. -/
theorem eq3_sandwich (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (htinf : Tendsto t atTop atTop)
    (f : ℕ → ℝ → ℝ) (s : ℕ → ℝ) (hI : CondI t f s)
    (hiii : ∀ n τ, 0 ≤ τ → 0 ≤ f n τ)
    (hiv : ∀ n, IntegrableOn (f n) (Set.Ici 0))
    (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (rate f) volume 0 T ∧
      finishedTotal t s (custTotal f) T ≤ ∫ τ in (0 : ℝ)..T, rate f τ ∧
      ∫ τ in (0 : ℝ)..T, rate f τ ≤ arrivedTotal t (custTotal f) T := by sorry

end HeymanStidham.HLG
