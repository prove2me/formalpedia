-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integral_cpow_mul_godementInner3_mulShift_eq_mul_Gamma_of_blockPoly_mul_colLinear_gaussian3
-- name    : LanglandsTunnell.CubicInduction.integral_cpow_mul_godementInner3_mulShift_eq_mul_Gamma_of_blockPoly_mul_colLinear_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/20ab59b6-c011-53dc-b38d-88c6fc54c50b
-- title:
--   Tate–Mellin evaluation of a linear-section Godement integral
-- statement:
--   Let $a\in\mathbb{Q}$ be non-zero and let $\psi_\infty$ be an additive character of the infinite adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$, assumed to satisfy $\psi_\infty(x)=\psi_{\mathrm{arch}}(a\,x)$ for all $x$, where $\psi_{\mathrm{arch}}$ is the standard archimedean character, the finite product over the infinite places of $x\mapsto\exp(2\pi i\,x)$ through the real embedding. Let $p_0,p_1$ be complex polynomials in variables indexed by $\mathrm{Fin}\,2\times\mathrm{Fin}\,2$, and let $S$ on real $2\times 3$ matrices be $S(M)=\bigl(p_0(M_{\bullet\bullet})M_{02}+p_1(M_{\bullet\bullet})M_{12}\bigr)\exp\bigl(-\pi\sum_{i<2,\,b<3}M_{ib}^2\bigr)$, the polynomials being evaluated at the entries of the left $2\times2$ block of $M$. Let $e$ be a $2\times2$ real array with $\det e\neq0$ and let $w\in\mathbb{C}$ satisfy $-1<\operatorname{Re}(w+1)$. Then $\int_{(0,\infty)} y^{w}\,\bigl(\int_{\mathbb{R}^2}S\bigl(e\cdot[\,I_2\mid v\,]\bigr)\,\psi_\infty\bigl(y\cdot(-v_1)\bigr)\,dv\bigr)\,dy$, the inner integral being `godementInner3` for the character $\psi_\infty$ shifted by the infinite adele with constant component $y$, at $h=e$ and $m=1$, equals $$\bigl(p_0(e)\rho_0+p_1(e)\rho_1\bigr)\,e^{-\pi\sum_{i,j}e_{ij}^2}\,|\det e|^{-1}\,(-ia)\cdot\tfrac12\bigl(\pi a^2(\rho_0^2+\rho_1^2)\bigr)^{-(w+1+1)/2}\,\Gamma\bigl((w+1+1)/2\bigr),$$ where $(\rho_0,\rho_1)$ is the second row of $e^{-1}$, real scalars being coerced to $\mathbb{C}$ and the powers being complex powers.
--
--   This is the archimedean Tate–Mellin computation for a Godement-type section whose last-column factor is an arbitrary linear form with coefficients polynomial in the left $2\times2$ block, extending the harmonic cases $\rho_0\pm i\rho_1$ of degree one. It is used in the Rankin–Selberg unfolding step [`LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_minorSection_gaussian3`](thm.html#LanglandsTunnell.RankinSelberg.exists_forall_unfoldedTorusPair_eq_setIntegral_iwasawa_tateM_of_minorSection_gaussian3), where the minor-section datum is of exactly this shape.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integral_cpow_mul_godementInner3_mulShift_eq_mul_Gamma_of_blockPoly_mul_colLinear_gaussian3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse MeasureTheory

theorem LanglandsTunnell.CubicInduction.integral_cpow_mul_godementInner3_mulShift_eq_mul_Gamma_of_blockPoly_mul_colLinear_gaussian3
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (p₀ p₁ : MvPolynomial (Fin 2 × Fin 2) ℂ)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
      (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((M v.1 (Fin.castSucc v.2) : ℝ) : ℂ)) p₀ * ((M 0 2 : ℝ) : ℂ) +
        MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((M v.1 (Fin.castSucc v.2) : ℝ) : ℂ)) p₁ * ((M 1 2 : ℝ) : ℂ)) *
        gaussian3 M)
    (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0)
    (w : ℂ) (hw : -1 < (w + 1).re) :
    (∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ w *
        godementInner3 (psiInf.mulShift (AutomorphicForm.StandardKernel.ofReal y)) S (Matrix.of e) 1)
      = (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) p₀ * (((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) +
          MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) p₁ * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ j : Fin 2, e i j ^ 2)) : ℂ) *
          (((|(Matrix.of e).det|)⁻¹ : ℝ) : ℂ) *
          (-Complex.I * (a : ℂ)) *
          ((1 / 2 : ℂ) *
            ((Real.pi * (a : ℝ) ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2) : ℝ) : ℂ)
                ^ (-((w + 1 + 1) / 2)) *
            Complex.Gamma ((w + 1 + 1) / 2)) := by sorry
