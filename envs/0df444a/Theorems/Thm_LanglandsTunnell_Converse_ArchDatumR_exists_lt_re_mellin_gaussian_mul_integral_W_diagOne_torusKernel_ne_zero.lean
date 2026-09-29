-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_lt_re_mellin_gaussian_mul_integral_W_diagOne_torusKernel_ne_zero
-- name    : LanglandsTunnell.Converse.ArchDatumR.exists_lt_re_mellin_gaussian_mul_integral_W_diagOne_torusKernel_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/0c0ad014-551d-56ed-85e4-b57a1e07b202
-- title:
--   Mellin non-vanishing of a Gaussian torus transform beyond any abscissa
-- statement:
--   Let $P_2$ be a real archimedean parameter and $D$ an `ArchDatumR P₂`, i.e. a function $W\colon M_2(\mathbb R)\to\mathbb C$, smooth on the invertible locus, transforming by the additive character under left translation by upper unipotents and by $z\mapsto \mathrm{centralChar}\,P_2(z)\,|z|$ under scaling, together with entire zeta functions $\zeta(g,u,a,\cdot)$ representing the twisted zeta integrals of $W$ up to the archimedean factor of $P_2.\mathrm{twist}\,u\,a$, satisfying the functional equation with epsilon factor under $g\mapsto wg$, $(u,a,s)\mapsto(-(u+P_2.\mathrm{centralExponent}),a+P_2.\mathrm{centralSign},1-s)$, of finite order in vertical strips, and with the stated derivative decay bounds at $\infty$ and at $0$. Assume $P_2=\mathrm{principal}(u_1,c,u_2,c)$ with $u_1,u_2\in\mathbb C$ and $c\in\mathbb Z/2$; that the torus profile satisfies $W(\mathrm{diag}(-\tau,1))=(-1)^{c}W(\mathrm{diag}(\tau,1))$ for $\tau\neq0$; that $W(xr)=W(x)$ for all $x\in GL_2(\mathbb R)$ and all $r$ in the subgroup `rowIsometrySubgroup₀ ℝ`; and that $W$ is non-zero at some $g\in GL_2(\mathbb R)$. Let $a\neq0$ be real, $\nu\in\mathbb C$, and let $H\colon\mathbb R\to\mathbb C$ be given by $$H(\sigma')=e^{-\pi a^2\sigma'^2}\int_0^\infty W\bigl(\mathrm{diag}(a\sigma'/w,1)\bigr)\,\mathrm{centralChar}\,P_2(w)\,|w|\,w^{\nu}\,e^{-\pi(w^{-2}+a^2w^2)}\,dw,$$ assumed continuous on $(0,\infty)$. Then for every $x_0\in\mathbb R$ there exists $s\in\mathbb C$ with $\operatorname{Re} s>x_0$ and $\mathcal M H(s-1)=\int_0^\infty \sigma'^{\,s-2}H(\sigma')\,d\sigma'\neq0$.
--
--   This is the archimedean non-vanishing input for the converse-theorem step: the Gaussian-weighted multiplicative convolution of a weight-zero real Whittaker profile against a Bessel-type torus kernel has Mellin transform not identically zero in any right half-plane. It is used in the cubic-induction arguments producing admissible twists for which the archimedean zeta vector of the constructed automorphic object is non-zero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_exists_lt_re_mellin_gaussian_mul_integral_W_diagOne_torusKernel_ne_zero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib.Analysis.MellinTransform

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

open LanglandsTunnell.Converse.ArchR Set in

theorem LanglandsTunnell.Converse.ArchDatumR.exists_lt_re_mellin_gaussian_mul_integral_W_diagOne_torusKernel_ne_zero
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (u₁ u₂ : ℂ) (c : ZMod 2) (hP : P₂ = RealArchParam.principal u₁ c u₂ c)
    (hpar : ∀ τ : ℝ, τ ≠ 0 → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0)
    (a : ℝ) (ha : a ≠ 0) (ν : ℂ)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * a ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          D.W (ArchR.diagOne (a * (σ' / w))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ν *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + a ^ 2 * w ^ 2))) : ℂ))
    (hHc : ContinuousOn H (Set.Ioi 0)) (x₀ : ℝ) :
    ∃ s : ℂ, x₀ < s.re ∧ mellin H (s - 1) ≠ 0 := by sorry
