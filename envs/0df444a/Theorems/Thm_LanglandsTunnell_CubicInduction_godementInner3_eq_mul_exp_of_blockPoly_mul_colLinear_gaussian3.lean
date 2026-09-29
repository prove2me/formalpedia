-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3
-- name    : LanglandsTunnell.CubicInduction.godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/63a2e61b-d706-5be5-8b92-3ba26439b673
-- title:
--   Godement inner integral of a column-linear Gaussian section
-- statement:
--   Let $a$ be a rational number (no non-vanishing hypothesis is imposed) and let $\psi_\infty$ be an additive character of the infinite adele ring of $\mathbb{Q}$ which satisfies $\psi_\infty(x) = \mathrm{psiArch}(a\,x)$ for all $x$, where [`NumberField.StandardAddChar.psiArch`](def/NumberField_StandardGlobalAddCharRat.html#L556) is the product over the infinite places of $\mathbb{Q}$ of the characters $x \mapsto \exp(2\pi i x)$ on the real completions. Let $p_0, p_1$ be complex polynomials in the four variables indexed by $\mathrm{Fin}\,2 \times \mathrm{Fin}\,2$, and let $S$ be the function on real $2\times 3$ matrices given by $S(M) = \bigl(p_0(M')\,M_{02} + p_1(M')\,M_{12}\bigr)\exp\bigl(-\pi\sum_{i<2}\sum_{b<3} M_{ib}^2\bigr)$, where $M'$ denotes the left $2\times 2$ block of $M$, i.e. the entries $M_{i\,\iota(j)}$ with $\iota$ the inclusion $\mathrm{Fin}\,2 \hookrightarrow \mathrm{Fin}\,3$ by `Fin.castSucc`. Let $e$ be a $2\times 2$ real array with $\det e \neq 0$. Then `godementInner3` at the character $\psi_\infty$, the section $S$, the matrix $e$ and the identity $3\times 3$ matrix, namely the integral over $v \in \mathbb{R}^2$ of $S$ evaluated at the matrix with rows $e\cdot(1,0,v_0)$ and $e\cdot(0,1,v_1)$ — that is, at the $2\times 3$ matrix $[\,e \mid ev\,]$ — times $\psi_\infty$ of the adele with every infinite component $-v_1$, equals $$\bigl(p_0(e)\rho_0 + p_1(e)\rho_1\bigr)\,\exp\Bigl(-\pi\sum_{i,j<2} e_{ij}^2\Bigr)\,|\det e|^{-1}\,(-ia)\,\exp\bigl(-\pi a^2(\rho_0^2+\rho_1^2)\bigr),$$ where $\rho_0 = (e^{-1})_{10}$, $\rho_1 = (e^{-1})_{11}$ is the second row of $e^{-1}$ and $p_0(e), p_1(e)$ denote evaluation at the complexified entries of $e$.
--
--   This is the archimedean inner integral along the unipotent radical occurring in the Godement-type zeta integral attached to a Schwartz section on $2\times 3$ matrices, evaluated at a fixed dilate of the Gaussian and an undilated character; it is the fixed-character core from which the Mellin-transformed (Tate-style) statements are obtained by replacing $a$ by $ay$. It feeds the lemmas expressing the Jacquet vectors `jacquetVector3` attached to block-harmonic times column-linear Gaussian data as explicit integrals, and through them the archimedean zeta computations of the cubic induction; the only input it uses is the two-dimensional Fourier transform identity `integral_colHarmonic_pow_mul_gaussian_mul_fourierChar_fin_two` for powers of $u_0 \pm i u_1$ against a Gaussian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse MeasureTheory LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.godementInner3_eq_mul_exp_of_blockPoly_mul_colLinear_gaussian3
    (a : ℚ)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    (p₀ p₁ : MvPolynomial (Fin 2 × Fin 2) ℂ)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
      (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((M v.1 (Fin.castSucc v.2) : ℝ) : ℂ)) p₀ * ((M 0 2 : ℝ) : ℂ) +
        MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((M v.1 (Fin.castSucc v.2) : ℝ) : ℂ)) p₁ * ((M 1 2 : ℝ) : ℂ)) *
        gaussian3 M)
    (e : Fin 2 → Fin 2 → ℝ) (he : (Matrix.of e).det ≠ 0) :
    godementInner3 psiInf S (Matrix.of e) 1
      = (MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) p₀ * (((Matrix.of e)⁻¹ 1 0 : ℝ) : ℂ) +
          MvPolynomial.eval (fun v : Fin 2 × Fin 2 => ((e v.1 v.2 : ℝ) : ℂ)) p₁ * (((Matrix.of e)⁻¹ 1 1 : ℝ) : ℂ)) *
          (Real.exp (-(Real.pi * ∑ i : Fin 2, ∑ j : Fin 2, e i j ^ 2)) : ℂ) *
          (((|(Matrix.of e).det|)⁻¹ : ℝ) : ℂ) *
          (-Complex.I * (a : ℂ)) *
          (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * (((Matrix.of e)⁻¹ 1 0) ^ 2 + ((Matrix.of e)⁻¹ 1 1) ^ 2))) : ℂ) := by sorry
