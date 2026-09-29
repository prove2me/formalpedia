-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_blockHarmonicOne_colHarmonic_gaussian3_of_weightZero
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_of_blockHarmonicOne_colHarmonic_gaussian3_of_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/33f841d8-b404-5001-8e07-a660f27fe1f4
-- title:
--   Jacquet vector at 1 of the harmonic Gaussian section, weight zero
-- statement:
--   Let $a$ be a non-zero rational number and let $\psi_\infty$ be an additive character of the infinite adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$ satisfying $\psi_\infty(x)=\mathrm{psiArch}(a\cdot x)$ for all $x$, where $\mathrm{psiArch}$ is the standard archimedean character. Let $P_2$ be a real archimedean parameter (principal or discrete) and let $D$ be an archimedean datum `ArchDatumR` for $P_2$, so $D.W$ is a function on $2\times 2$ real matrices, smooth on the invertible locus, transforming by $\psi$ under left unipotent translation and by $\mathrm{centralChar}\,P_2(z)\,|z|$ under scaling by $z\neq 0$, equipped with entire completed zeta integrals satisfying the functional equation of $P_2$ and the prescribed growth and decay bounds; assume $D.W$ is right invariant under the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$, i.e. $D.W(x r)=D.W(x)$ for all $r$ in that subgroup (weight zero). Let $u_3\in\mathbb{C}$, $a_3\in\mathbb{Z}/2$, and let $S$ on $2\times 3$ real matrices be $$S(M)=\bigl((M_{00}+iM_{10})-i(M_{01}+iM_{11})\bigr)\,(M_{02}-iM_{12})^{1}\,e^{-\pi\sum_{i,b}M_{ib}^{2}},$$ the product of a harmonic polynomial in the first $2\times 2$ block, a linear antiholomorphic factor in the third column, and `gaussian3`. Then for every real $y\neq 0$ the Jacquet vector `jacquetVector3 D u₃ a₃ (a*y) psiInf S` evaluated at the identity of $GL_3$ of the infinite adeles — that is, $\mathrm{quasiChar}(u_3+1,a_3)$ of the determinant of the real matrix attached to the argument, times the integral over $e\in M_2(\mathbb{R})$ of `jacquetIntegrand3` — equals $$2\pi(-a)\int_{\mathbb{R}}\int_{0}^{\infty}\mathrm{quasiChar}(u_3+2,a_3)\bigl((y_1y_2)^{-1}\bigr)\,y_2^{2}\Bigl(\tfrac1{y_1}+\tfrac1{y_2}-a y y_1\Bigr)e^{-\pi(y_1^{-2}+y_2^{-2}+a^2y_2^{2}+a^2y^2y_1^{2})}\,\mathrm{centralChar}(P_2)(y_2)\,|y_2|\;D.W\!\begin{pmatrix}ayy_1/y_2&0\\0&1\end{pmatrix}\,dy_2\,dy_1,$$ where $\mathrm{quasiChar}(u,\alpha)(t)=|t|^{u}$ times $\operatorname{sign}(t)$ when $\alpha\neq 0$.
--
--   This is the archimedean computation, in the weight-zero case, of the Whittaker (Jacquet) vector attached to the cubic-induction Godement section built from a harmonic block polynomial and a linear column factor times a Gaussian: the triple integral over the $2\times 2$ matrix variable collapses, after an Iwasawa decomposition, to an explicit double integral over a torus with the bracket $1/y_1+1/y_2-ayy_1$. It feeds the identification of the archimedean zeta integral of this vector as a gamma factor times an explicit Mellin transform, used in turn to show that the archimedean factor does not vanish identically.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_blockHarmonicOne_colHarmonic_gaussian3_of_weightZero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell LanglandsTunnell.CubicInduction MeasureTheory

theorem LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_of_blockHarmonicOne_colHarmonic_gaussian3_of_weightZero
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ))) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 1) * gaussian3 M)
    (y : ℝ) (hy : y ≠ 0) :
    jacquetVector3 D u₃ a₃ ((a : ℝ) * y) psiInf S 1 =
      2 * (Real.pi : ℂ) * (-(a : ℂ)) *
        ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ),
          ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ *
            (((y₂ ^ 2 * (y₁⁻¹ + y₂⁻¹ - (a : ℝ) * y * y₁)) : ℝ) : ℂ) *
            (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
            (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) := by sorry
