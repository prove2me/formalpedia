-- Prove2me | Theorems.Thm_HeymanStidham_HLG_rate_pos_sub_neg_integral
-- name    : HeymanStidham.HLG.rate_pos_sub_neg_integral
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:39:20.36805+00:00
-- url     : https://prove2.me/theorems/f91c64e1-2a80-4343-ba98-a2239040bfa8
-- title:
--   Proof of THEOREM 2, p. 987 — ∫₀ᵀ h⁺ − ∫₀ᵀ h⁻ = ∫₀ᵀ h
-- statement:
--   Let $0 \le t_1 \le t_2 \le \cdots$ be arrival epochs with $t_n \to \infty$. For each customer $n$ let $f_n$ be a real function on $[0,\infty)$ and $s_n \ge 0$ such that (i) $f_n(t) = 0$ for $t \notin [t_n, t_n+s_n]$ and (v) $\int_0^\infty |f_n(t)|\,dt < \infty$. Let $f_n^\pm = \max[0, \pm f_n]$, $h^\pm(t) = \sum_n f_n^\pm(t)$ and $h(t) = \sum_n f_n(t)$. Then for every $T \ge 0$ the functions $h^+$, $h^-$ and $h$ are integrable on $[0,T]$, and
--
--   $$
--   \int_0^T h^+(t)\,dt - \int_0^T h^-(t)\,dt = \int_0^T h(t)\,dt.
--   $$
--
--   In the proof of Theorem 2 this identity, obtained from monotone convergence and Fubini's theorem, is what turns $H^+ - H^-$ into the time average of $h$.
--
--   **Formalization Note** The page derives the finiteness of $\int_0^T h^\pm$ from $H^\pm < \infty$. Here it is a conclusion: under (i), (v) and $t_n \to \infty$ (a consequence of (2) in the paper's setting) only finitely many $f_n$ are nonzero on $[0,T]$.
-- source:
--   Heyman and Stidham, The relation between customer and time averages in queues, Oper. Res. 28 (1980), p. 987, proof of Theorem 2 (the displays after G(ω) = G⁺(ω) − G⁻(ω))

import Mathlib
import Definitions.Def_HeymanStidham_HLG_Setting

open Filter Topology MeasureTheory

namespace HeymanStidham.HLG

/-- Proof of THEOREM 2, p. 987: under (i) and (v), with arrival epochs tending to infinity,
`h⁺`, `h⁻` and `h` are integrable on `[0, T]` and `∫₀^T h⁺ − ∫₀^T h⁻ = ∫₀^T h`. -/
theorem rate_pos_sub_neg_integral (t : ℕ → ℝ) (ht : Monotone t) (ht0 : 0 ≤ t 0)
    (htinf : Tendsto t atTop atTop)
    (f : ℕ → ℝ → ℝ) (s : ℕ → ℝ) (hI : CondI t f s)
    (hv : ∀ n, IntegrableOn (f n) (Set.Ici 0))
    (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (rate (posPartFn f)) volume 0 T ∧
      IntervalIntegrable (rate (negPartFn f)) volume 0 T ∧
      IntervalIntegrable (rate f) volume 0 T ∧
      (∫ τ in (0 : ℝ)..T, rate (posPartFn f) τ) - (∫ τ in (0 : ℝ)..T, rate (negPartFn f) τ) =
        ∫ τ in (0 : ℝ)..T, rate f τ := by sorry

end HeymanStidham.HLG
