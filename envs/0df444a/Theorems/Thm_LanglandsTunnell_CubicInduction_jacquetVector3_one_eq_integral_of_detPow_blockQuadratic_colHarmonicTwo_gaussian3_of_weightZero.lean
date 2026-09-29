-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/2a964417-f9a8-523e-bf39-9bfade90a7f4
-- title:
--   Torus unfolding of a GL₃ Jacquet vector at the identity
-- statement:
--   Let $a$ be a nonzero rational number and let $\psi_\infty$ be an additive character of the infinite adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$ satisfying $\psi_\infty(x)=\mathrm{psiArch}(a\,x)$ for all $x$. Let $P_2$ be a real archimedean parameter and $D$ an `ArchDatumR P₂`, i.e. a Whittaker function $W=D.W$ on $2\times 2$ real matrices that is smooth on the invertible locus, transforms by $\psi$ under left unipotent translation and by $\mathrm{centralChar}\,P_2(z)\,|z|$ under scaling, and whose zeta integrals are entire of finite order with the prescribed functional equation and decay; assume in addition $W(x r)=W(x)$ for every $r$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$ and every $x\in GL_2(\mathbb{R})$. Let $u_3\in\mathbb{C}$, $a_3\in\mathbb{Z}/2$, $\delta\in\mathbb{N}$, and let $S$ be the section $$S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\bigl((M_{00}+iM_{10})^2+(M_{01}+iM_{11})^2\bigr)(M_{02}-iM_{12})^2 e^{-\pi\sum_{i,b}M_{ib}^2}$$ on $2\times 3$ real matrices. Then for every real $y\neq 0$ the Jacquet vector $\mathrm{jacquetVector3}\,D\,u_3\,a_3\,(ay)\,\psi_\infty\,S$ evaluated at the identity of $GL_3$ equals $$2\pi a^2\int_{\mathbb{R}}\int_{0}^{\infty}\chi_{u_3+2,a_3}\bigl((y_1y_2)^{-1}\bigr)\,y_2^3 (y_1y_2)^{-\delta}\Bigl(\tfrac1{y_1^2}-\tfrac1{y_2^2}+\tfrac{2ayy_1}{y_2}-a^2y^2y_1^2+\tfrac1{2\pi}\Bigr)e^{-\pi(y_1^{-2}+y_2^{-2}+a^2y_2^2+a^2y^2y_1^2)}\,\mathrm{centralChar}\,P_2(y_2)\,|y_2|\;W\!\begin{pmatrix}ayy_1/y_2&0\\0&1\end{pmatrix}\,dy_2\,dy_1,$$ where $\chi_{u,a}(t)=|t|^{u}$ times $1$ if $a=0$ and $\operatorname{sign}(t)$ otherwise.
--
--   This is the unfolding, in Iwasawa coordinates on the $2\times2$ integration variable, of the archimedean Jacquet integral attached to the given polynomial-times-Gaussian section of column degree $2$ and block factor $z_0^2+z_1^2$ decorated by $\det^{\delta}$: the fourfold integral collapses to a double integral over the torus coordinates $y_1\in\mathbb{R}$, $y_2>0$ against the $GL_2$ Whittaker function of $D$ on the diagonal. It feeds the construction of the associated archimedean zeta integral and its nonvanishing, used in the converse-theorem step for the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero.lean

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

theorem LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2) (δ : ℕ)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) ^ 2 + (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ)) ^ 2) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 2) * gaussian3 M)
    (y : ℝ) (hy : y ≠ 0) :
    jacquetVector3 D u₃ a₃ ((a : ℝ) * y) psiInf S 1 =
      2 * (Real.pi : ℂ) * (a : ℂ) ^ 2 *
        ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ),
          ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ *
            (((y₂ ^ 3 * ((y₁ * y₂)⁻¹) ^ δ * ((y₁ ^ 2)⁻¹ - (y₂ ^ 2)⁻¹ + 2 * (a : ℝ) * y * y₁ / y₂ - (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2 + (2 * Real.pi)⁻¹)) : ℝ) : ℂ) *
            (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
            (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) := by sorry
