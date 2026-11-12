-- Prove2me | Theorems.Thm_Helfgott_etaStar_tao_minorArc_radius
-- name    : Helfgott.etaStar_tao_minorArc_radius
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-11T16:51:22.939213+00:00
-- url     : https://prove2.me/theorems/4ba02573-bdb4-4278-8742-93be35196175
-- title:
--   A radius-dependent Tao-type bound outside the actual Goldbach major arcs
-- statement:
--   Let $X=x/49$, with $x\ge49$, $t>0$ and $Xt\ge10^{20}$. Suppose $r\ge400$, $28r\le x$, and $rt\ge1400$. For every $\alpha$ outside the actual parity-dependent major arcs $\mathfrak M_{8,r}(x)$, put
--
--   $$L=\log X,\quad A=\frac{0.14}{\sqrt{r/4}},\quad B=\frac{0.64}{\sqrt{r/14}},\quad C=0.15X^{-1/5},$$
--   $$D_0=A+B/2+4C/5,\quad D_{-1}=B/2+C/5,\quad H=L(L+11.3),\quad J=2L+11.3.$$
--
--   Then the actual Gaussian Mellin smoothing satisfies
--
--   $$|S_{\eta_*}(x,\alpha)|\le X\left[D_0\left((H+3)\sqrt{\pi/2}+2J\right)+D_{-1}\left(J\sqrt{\pi/2}+H+2\right)+5t^3\right].$$
--
--   The rational approximation is supplied by the proof; it is not an additional hypothesis. The bound decreases with the radius, but its logarithmic losses mean that it is an outer-arc auxiliary estimate, not a proof of the final weighted minor-arc budget.
-- source:
--   Derived from the proved Helfgott.etaStar_tao_gaussian_bound by Mathlib Dirichlet approximation. The proof normalizes rational centers on the additive circle, handles the odd/even widths of the actual arc definition, and chooses N=ceil(x/(4r)).

import Definitions.Def_Helfgott_ArcCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Helfgott

theorem Helfgott.etaStar_tao_minorArc_radius (x t α : ℝ) (r : ℕ)
    (hx : 49 ≤ x) (ht : 0 < t) (hmin : (10:ℝ)^20 ≤ x*t/49)
    (hr : 400 ≤ r) (hrx : 28*(r:ℝ) ≤ x) (hrt : 1400 ≤ (r:ℝ)*t)
    (hminor : (α : AddCircle (1:ℝ)) ∉ majorArcs 8 r x) :
    let X := x/49
    let L := Real.log X
    let A := (7/50:ℝ)/Real.sqrt ((r:ℝ)/4)
    let B := (16/25:ℝ)/Real.sqrt ((r:ℝ)/14)
    let C := (3/20:ℝ)*X^(-(1/5:ℝ))
    let D₀ := A+B/2+4*C/5
    let Dm := B/2+C/5
    let H := L*(L+113/10)
    let J := 2*L+113/10
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n:ℝ)/x):ℝ):ℂ))
      (α : AddCircle (1:ℝ))‖ ≤
      X*(D₀*((H+3)*Real.sqrt (Real.pi/2)+2*J) +
        Dm*(J*Real.sqrt (Real.pi/2)+H+2)+5*t^3) := by sorry
