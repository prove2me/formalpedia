-- Prove2me | Theorems.Thm_LanglandsTunnell_add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor
-- name    : LanglandsTunnell.add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/b1d4de82-377f-5662-bce1-7c18ce1c896b
-- title:
--   One-parity Whittaker sheet is the Gaussian convolution profile
-- statement:
--   Let $u_1,u_2\in\mathbb C$, let $a_1,a_2\in\mathbb Z/2$, let $W:\mathbb R\to\mathbb C$ be continuous on $\{t\in\mathbb R: t\neq 0\}$, and fix a single parity $b\in\mathbb Z/2$. Write $[a]=$ `signShift` $a$, that is $0$ if $a=0$ and $1$ otherwise, and set $F(t)=\bigl(W(t)+(-1)^{b.\mathrm{val}}W(-t)\bigr)/t$. Assume there is a real $s_0$ such that for every $s\in\mathbb C$ with $\operatorname{Re} s>s_0$ the Mellin integral of $F$ converges at $s$ and $$\int_0^\infty F(t)\,t^{s-1}\,dt=\Gamma_{\mathbb R}\bigl(s+(u_1+0)+[a_1+b]\bigr)\,\Gamma_{\mathbb R}\bigl(s+(u_2+0)+[a_2+b]\bigr),$$ the archimedean factor of the parameter obtained from $\mathrm{principal}(u_1,a_1,u_2,a_2)$ by twisting by $(0,b)$, whose $\Gamma_{\mathbb C}$-part is empty. Then for every $t>0$ the corresponding parity sheet of $W$ is given by the explicit Gaussian convolution integral $$W(t)+(-1)^{b.\mathrm{val}}W(-t)=t\cdot 4\int_0^\infty r^{\,u_1+[a_1+b]}e^{-\pi r^2}\,(t/r)^{\,u_2+[a_2+b]}e^{-\pi (t/r)^2}\,\frac{dr}{r},$$ the inner powers being complex powers of the positive reals $r$ and $t/r$.
--
--   This is the single-parity form of the archimedean Whittaker profile identification: knowing the Mellin transform of one parity sheet of $W$ on a right half-plane pins that sheet down as the Gaussian convolution attached to a principal-series parameter, by Mellin uniqueness together with the computation of the Mellin transform of the Gaussian convolution. It is used in the Rankin–Selberg archimedean computations that evaluate dual-torus pairings in terms of root numbers and $\Gamma$-factors, in situations where only the sheet of one parity is available, as for even principal-series (Maass) parameters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor.lean

import Definitions.Def_LanglandsTunnell_ArchParam
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.MellinInversion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Real
open LanglandsTunnell

theorem LanglandsTunnell.add_pow_mul_apply_neg_eq_mul_mulConvGaussian_of_mellin_sheet_eq_archFactor
    (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2) (W : ℝ → ℂ)
    (hWc : ContinuousOn W {t : ℝ | t ≠ 0}) (b : ZMod 2)
    (hMel : ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      MellinConvergent (fun t : ℝ => (W t + (-1 : ℂ) ^ b.val * W (-t)) / (t : ℂ)) s ∧
        mellin (fun t : ℝ => (W t + (-1 : ℂ) ^ b.val * W (-t)) / (t : ℂ)) s
          = ((RealArchParam.principal u₁ a₁ u₂ a₂).twist 0 b).archFactor s)
    (t : ℝ) (ht : 0 < t) :
    W t + (-1 : ℂ) ^ b.val * W (-t) =
      (t : ℂ) * ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
        ((r : ℂ) ^ (u₁ + signShift (a₁ + b)) * (Real.exp (-(π * r ^ 2)) : ℂ)) *
          (((t / r : ℝ) : ℂ) ^ (u₂ + signShift (a₂ + b)) * (Real.exp (-(π * (t / r) ^ 2)) : ℂ)) / (r : ℂ)) := by sorry
