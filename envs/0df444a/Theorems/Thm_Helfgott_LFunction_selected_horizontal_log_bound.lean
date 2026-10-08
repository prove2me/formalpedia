-- Prove2me | Theorems.Thm_Helfgott_LFunction_selected_horizontal_log_bound
-- name    : Helfgott.LFunction_selected_horizontal_log_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T15:02:50.855805+00:00
-- url     : https://prove2.me/theorems/133876b9-907e-4dd2-851d-2db0847e3285
-- title:
--   Quantitative common horizontal contour heights for every Dirichlet L-function
-- statement:
--   Let $\chi$ be any Dirichlet character of positive modulus, including a principal character. There is a finite constant $C\ge0$ such that, for every $T\ge8$, some $u\in(T,T+1)$ satisfies $L(s,\chi)\ne0$ and
--
--   \[\left|\frac{L'(s,\chi)}{L(s,\chi)}\right|\le C(1+T)^2\qquad(-1/2\le\Re s\le2,\ \Im s=\pm u).\]
--
--   The same height works on both horizontal edges, uniformly over their full real interval. This is a quantitative input to the infinite-height contour shift for the actual Goldbach smoothings; the numerical zero contributions and Goldbach major-arc residual remain separate.
-- source:
--   Helfgott, Major arcs for Goldbach’s problem, https://arxiv.org/abs/1305.2897. Mathlib Jensen, divisors, canonical decomposition and Borel-Caratheodory contributors including Stefan Kebekus; full L-function/Mellin functional equations including David Loeffler and contributors; complex logarithmic derivative, primitives, gamma reflection and Euler series contributors. Complete original common height selection and quantitative assembly. Written by Codex.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
open Complex

theorem Helfgott.LFunction_selected_horizontal_log_bound (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ T : ℝ,8 ≤ T →
      ∃ u : ℝ,T<u ∧ u<T+1 ∧ ∀ σ v : ℝ,
        -(1/2 : ℝ) ≤ σ → σ ≤ 2 → (v=u ∨ v=-u) →
        χ.LFunction ((σ : ℂ)+(v : ℂ)*I) ≠ 0 ∧
        ‖deriv χ.LFunction ((σ : ℂ)+(v : ℂ)*I)/
          χ.LFunction ((σ : ℂ)+(v : ℂ)*I)‖ ≤ C*(1+T)^2 := by sorry
