-- Prove2me | Theorems.Thm_MasulloRH_critical_line_jet_convolution_trace
-- name    : MasulloRH.critical_line_jet_convolution_trace
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:58:54.079325+00:00
-- url     : https://prove2.me/theorems/67cc7e09-c401-4950-b3ec-0d63b4905ced
-- title:
--   Mellin trace on all admissible critical-line zeta jets with the exact Sobolev weight
-- statement:
--   Let $p>1/2$, $w(x)=(1+x^2)^{-p/2}$, and let $Z$ be the set of distinct critical-line zeros of the Riemann zeta function. For $\rho\in Z$ put $d_\rho=\min\{\operatorname{ord}_\rho\zeta,\lceil p-1/2\rceil\}$. In $L^2(\mathbb R,dx)$ take the closed span of the functions $w(x)x^r e^{i\operatorname{Im}(\rho)x}$ with $0\le r<d_\rho$.
--
--   For every smooth test $\varphi$ compactly supported in $(0,\infty)$ with $\varphi(1)=0$, integrating $u(x)\mapsto w(x)u(x+y)/w(x+y)$ against $\varphi(e^y)\,dy$ defines a unique bounded operator $T$ on that span. It is nuclear, and
--   $$
--   \operatorname{Tr}(T)=\sum_{\rho\in Z}d_\rho\,\mathcal M\varphi(\rho-1/2)
--   $$
--   with absolute convergence. In the draft’s Sobolev parameter $s=2p$, the admissible jet orders satisfy $2r+1<s$, including when $(s-1)/2$ is an integer. The space in this statement is the explicitly generated critical-line jet space.
-- source:
--   A. Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Theorem 1, Corollary 2 and Appendix I, preprint pp. 65–68, equations (29)–(38), https://arxiv.org/abs/math/9811068. Critical-line jet-space trace associated with Masullo, The Music of the Primes, §10.3.1, equations (10.3.1.3)–(10.3.1.4), using the strict Sobolev cutoff and frequency-band approach proposed by Calvin Yost-Wolff, Prove2Me mission comment d8680fb7-dd35-4a9c-ab4e-5888ec240d48.

import Mathlib
import Definitions.Def_MasulloGRH_HilbertNuclear
import Definitions.Def_MasulloRH_RationalTrace
open MeasureTheory Filter MasulloRH MasulloGRH
open scoped InnerProductSpace

theorem MasulloRH.critical_line_jet_convolution_trace (p : ℝ) (hp : 1 / 2 < p) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2}
    let H := Lp ℂ 2 (volume : Measure ℝ)
    let S := (Submodule.span ℂ {u : H | ∃ (ρ : Z) (r : ℕ), r < analyticOrderNatAt riemannZeta ρ.val ∧
      (r:ℝ)+1/2 < p ∧ (u : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
      ((1+x^2)^(-p/2) : ℝ) * ((x:ℂ)^r * Complex.exp (↑(ρ.val.im*x) * Complex.I))}).topologicalClosure
    ∃! T : S →L[ℂ] S,
      (∀ (u : S) (g : H), ⟪g, (T u : H)⟫_ℂ =
        ∫ y : ℝ, φ (Real.exp y) * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
          ((((1+x^2)^(-p/2) / (1+(x+y)^2)^(-p/2) : ℝ) : ℂ) * (u : H) (x+y))) ∧
      IsNuclearOperator T ∧ HasSum (fun ρ : Z =>
        ((min (analyticOrderNatAt riemannZeta ρ.val) ⌈p-1/2⌉₊ : ℕ) : ℂ) *
          mellin φ (ρ.val - 1/2)) (operatorTrace T) := by sorry
