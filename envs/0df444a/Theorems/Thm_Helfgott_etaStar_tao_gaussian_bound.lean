-- Prove2me | Theorems.Thm_Helfgott_etaStar_tao_gaussian_bound
-- name    : Helfgott.etaStar_tao_gaussian_bound
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T16:37:50.736783+00:00
-- url     : https://prove2.me/theorems/8e47d478-74ba-4f2d-bfb7-42ba991dcb4f
-- title:
--   An explicit Tao-type rational-phase bound for the Gaussian Mellin smoothing
-- statement:
--   Let $X=x/49$, with $x\ge49$, and choose $t>0$ so that $Xt\ge10^{20}$. Suppose
--
--   $$4\alpha=\frac aq+\beta,\qquad (|a|,q)=1,\qquad 100\le q\le\frac{Xt}{100},\qquad |\beta|\le q^{-2}.$$
--
--   Write $L=\log X$ and define
--
--   $$A=\frac{0.14}{\sqrt q},\quad B=\frac{0.64}{\sqrt{X/q}},\quad C=0.15X^{-1/5},$$
--   $$D_0=A+\frac B2+\frac{4C}{5},\quad D_{-1}=\frac B2+\frac C5,\quad H=L(L+11.3),\quad J=2L+11.3.$$
--
--   For the actual Helfgott smoothing $\eta_*=\eta_2*_M\varphi(49\,\cdot)$, where $\varphi(w)=w^2e^{-w^2/2}$, one has
--
--   $$|S_{\eta_*}(x,\alpha)|\le X\left[D_0\left((H+3)\sqrt{\pi/2}+2J\right)+D_{-1}\left(J\sqrt{\pi/2}+H+2\right)+5t^3\right].$$
--
--   This transfers the proved explicit compact-smoothing estimate of Tao to the actual Gaussian Mellin smoothing, retaining its scale dependence through explicit Gaussian moments. It is an auxiliary rational-phase estimate; no claim is made that it alone gives the complete weighted minor-arc budget.
-- source:
--   Derived from the proved TaoFivePrimes.exp_sum_estimate, Tao, Every odd number greater than 1 is the sum of at most five primes, arXiv:1201.6656, Theorem 1.3 (1.9), together with the proved Helfgott Mellin exponential-sum identity. The Gaussian transfer uses weighted arithmetic-geometric mean inequalities and exact Gaussian moments. This is a derived conservative bound, not the sharper compact-sum estimate of Helfgott. https://arxiv.org/abs/1201.6656 ; https://arxiv.org/html/1312.7748v2

import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_WeightedCounting
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Helfgott

theorem Helfgott.etaStar_tao_gaussian_bound (x t α β : ℝ) (a : ℤ) (q : ℕ)
    (hx : 49 ≤ x) (ht : 0 < t) (hmin : (10:ℝ)^20 ≤ x*t/49)
    (hq : 100 ≤ q) (hqx : (q:ℝ) ≤ (x*t/49)/100)
    (haq : Nat.Coprime a.natAbs q) (hα : 4*α = (a:ℝ)/q+β)
    (hβ : |β| ≤ 1/(q:ℝ)^2) :
    let X := x/49
    let L := Real.log X
    let A := (7/50:ℝ)/Real.sqrt q
    let B := (16/25:ℝ)/Real.sqrt (X/q)
    let C := (3/20:ℝ)*X^(-(1/5:ℝ))
    let D₀ := A+B/2+4*C/5
    let Dm := B/2+C/5
    let H := L*(L+113/10)
    let J := 2*L+113/10
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n:ℝ)/x):ℝ):ℂ))
      (α : AddCircle (1:ℝ))‖ ≤
      X*(D₀*((H+3)*Real.sqrt (Real.pi/2)+2*J) +
        Dm*(J*Real.sqrt (Real.pi/2)+H+2)+5*t^3) := by sorry
