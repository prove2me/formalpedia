-- Prove2me | Theorems.Thm_MasulloRH_critical_line_pure_mode_convolution_trace
-- name    : MasulloRH.critical_line_pure_mode_convolution_trace
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:50:32.300229+00:00
-- url     : https://prove2.me/theorems/42ee29d3-45a6-4932-95d8-94ce55eb28ed
-- title:
--   Nuclear Mellin trace on the pure critical-line zeta modes in weighted L²
-- statement:
--   Let $p>1/2$, set $w_p(x)=(1+|x|)^{-p}$, and let $Z$ be the set of distinct zeros of the Riemann zeta function with real part $1/2$. In $L^2(\mathbb R,dx)$ let $S$ be the closed linear span of $w_p(x)e^{i\operatorname{Im}(\rho)x}$ for $\rho\in Z$. Let $\varphi$ be smooth and compactly supported in $(0,\infty)$, with $\varphi(1)=0$.
--
--   Integrating the translations $u(x)\mapsto w_p(x)u(x+y)/w_p(x+y)$ against $\varphi(e^y)\,dy$ defines a unique bounded operator $T$ on $S$. This operator is nuclear and
--   $$
--   \operatorname{Tr}(T)=\sum_{\rho\in Z}\mathcal M\varphi(\rho-1/2).
--   $$
--   The series converges absolutely. Each distinct zero contributes one pure exponential mode. The theorem concerns the closed span of those modes on the critical line.
-- source:
--   Alain Connes, Trace formula in noncommutative geometry and the zeros of the Riemann zeta function, Corollary 2 and Appendix I, equations (35)–(38), https://arxiv.org/abs/math/9811068. The present pure-mode realization uses the smooth frequency-band argument discussed by Calvin Yost-Wolff for Masullo §10.3.1 on Prove2Me, comment d8680fb7-dd35-4a9c-ab4e-5888ec240d48, 20 Nov 2026.

import Mathlib
import Definitions.Def_MasulloGRH_HilbertNuclear
import Definitions.Def_MasulloRH_RationalTrace
open MasulloRH MasulloGRH MeasureTheory Filter
open scoped InnerProductSpace

theorem MasulloRH.critical_line_pure_mode_convolution_trace (p : ℝ) (hp : 1 / 2 < p) (φ : ℝ → ℂ) (hφ : MasulloRH.IsRationalTraceTest φ) :
    let Z := {ρ : ℂ // riemannZeta ρ = 0 ∧ ρ.re = 1/2}
    let H := Lp ℂ 2 (volume : Measure ℝ)
    let S := (Submodule.span ℂ {f : H | ∃ ρ : Z, (f : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
      (((1+|x|)^(-p) : ℝ) : ℂ) * Complex.exp (((ρ.val.im*x : ℝ) : ℂ) * Complex.I)}).topologicalClosure
    ∃! T : S →L[ℂ] S,
      (∀ (u : S) (g : H), ⟪g, (T u : H)⟫_ℂ =
        ∫ y : ℝ, φ (Real.exp y) * ∫ x : ℝ, (starRingEnd ℂ) (g x) *
          ((((1+|x|)^(-p) / (1+|x+y|)^(-p) : ℝ) : ℂ) * (u : H) (x+y))) ∧
      IsNuclearOperator T ∧ HasSum (fun ρ : Z => mellin φ (ρ.val - 1/2)) (operatorTrace T) := by sorry
