-- Prove2me | Theorems.Thm_Helfgott_etaTwo_finite_rectangular_integral_norm
-- name    : Helfgott.etaTwo_finite_rectangular_integral_norm
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-12T16:39:17.946555+00:00
-- url     : https://prove2.me/theorems/6944b735-fab6-46c9-9a79-3dbcb4f498af
-- title:
--   Exact rectangular integral bound for Helfgott smoothing
-- statement:
--   Let $S,T$ be finite sets of positive integers, $z_{d,m}$ arbitrary complex coefficients, and $y>0$. For Helfgott's compact smoothing $\eta_2(t)=4\max(\log 2-|\log(2t)|,0)$ on $t>0$, one has
--   $$\left|\sum_{d\in S}\sum_{m\in T}z_{d,m}\eta_2(dm/y)\right|\le4\int_0^\infty\left|\sum_{\substack{d\in S\\W/2\le d\le W}}\sum_{\substack{m\in T\\y/(2W)\le m\le y/W}}z_{d,m}\right|\frac{dW}{W}.$$
--   The smoothing is represented exactly by a Mellin convolution of two interval indicators. This bound retains the changing rectangular summation windows before applying estimates to the inner sum. All finite endpoints are included; the integral does not depend on the values at those endpoints.
-- source:
--   H. A. Helfgott, Minor arcs for Goldbach, https://arxiv.org/html/1205.5252, Section 4, equations (4.1)-(4.4). Generalization: arbitrary finite positive index sets and complex matrix coefficients in place of factorized Vaughan coefficients; the original bilinear application is a specialization. The formal inequality is the triangle inequality applied to the exact rectangular integral identity.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open Finset MeasureTheory
open scoped BigOperators Classical

theorem Helfgott.etaTwo_finite_rectangular_integral_norm
    (S T : Finset ℕ) (z : ℕ→ℕ→ℂ) (y : ℝ)
    (hS : ∀ d∈S, 0<d) (hT : ∀ m∈T, 0<m) (hy : 0<y) :
    ‖∑ d ∈ S, ∑ m ∈ T, z d m*(Helfgott.etaTwo ((d:ℝ)*(m:ℝ)/y):ℂ)‖≤
      4*∫ w in Set.Ioi (0:ℝ), (1/w)*
        ‖∑ d ∈ S.filter (fun d : ℕ=>w/2≤(d:ℝ) ∧ (d:ℝ)≤w),
          ∑ m ∈ T.filter (fun m : ℕ=>y/(2*w)≤(m:ℝ) ∧ (m:ℝ)≤y/w), z d m‖ := by sorry
