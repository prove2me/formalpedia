-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_minorSection_gaussian3_of_weightZero
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_of_minorSection_gaussian3_of_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/aa9887d2-f4e5-580c-8332-a184d25e32b3
-- title:
--   Minor-section Jacquet vector at 1 as an explicit double integral
-- statement:
--   Fix a nonzero rational $a$ and let $\psi_\infty$ be an additive character of the infinite adele ring of $\mathbb Q$ with $\psi_\infty(x)=\mathrm{psiArch}(a\,x)$ for all $x$. Let $D$ be an archimedean $GL_2$ datum `ArchDatumR` for a real archimedean parameter $P_2$ (a function $W$ on real $2\times 2$ matrices, smooth on the invertible locus, with the unipotent and central transformation laws, entire twisted zeta functions satisfying the functional equation and finite-order and decay bounds), and assume $W$ is right invariant under the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb R)$, i.e. $W(xr)=W(x)$ for all $r$ in that subgroup and all $x\in GL_2(\mathbb R)$ (weight zero). Let $u_3\in\mathbb C$, $a_3\in\mathbb Z/2$, and let $S$ be the minor-section test function on real $2\times 3$ matrices, $S(M)=\bigl((M_{00}-iM_{01})M_{12}-(M_{10}-iM_{11})M_{02}\bigr)\exp\bigl(-\pi\sum_{i,b}M_{ib}^2\bigr)$. Then for every real $y\neq 0$ the Jacquet vector `jacquetVector3` attached to $D,u_3,a_3$, dilation $ay$, character $\psi_\infty$ and $S$, evaluated at $g=1$ — by definition $\mathrm{quasiChar}(u_3+1,a_3)$ of the determinant of the real $3\times 3$ matrix of $g$ times the integral over $e\in\mathbb R^{2\times 2}$ of `jacquetIntegrand3` — equals $$2\pi(-ia)\int_{\mathbb R}\int_{0}^{\infty}\chi_{u_3+2,a_3}\bigl((y_1y_2)^{-1}\bigr)\,\frac{y_2^2}{y_1}\bigl(1-a y y_1^2\bigr)\,e^{-\pi(y_1^{-2}+y_2^{-2}+a^2y_2^2+a^2y^2y_1^2)}\,\omega_{P_2}(y_2)|y_2|\;W\!\begin{pmatrix}ayy_1/y_2&0\\0&1\end{pmatrix}\,dy_2\,dy_1,$$ where $\chi_{u,\epsilon}(t)=|t|^{u}$ times $\mathrm{sign}(t)$ when $\epsilon\neq 0$, and $\omega_{P_2}=\chi$ taken at the central exponent and central sign of $P_2$, so that $\omega_{P_2}(y_2)|y_2|$ is the factor occurring in the central law of $D$.
--
--   This is the archimedean Jacquet (Godement–Jacquet type) integral for the minor-section Gaussian test function on $2\times 3$ matrices, reduced in weight zero to a double integral over the Iwasawa torus coordinates after the angular and unipotent integrations have been carried out. It supplies the explicit torus function used by [`LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero`](thm.html#LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero), where the remaining integral is identified with a gamma factor times a Mellin transform.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_minorSection_gaussian3_of_weightZero.lean

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

theorem LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_of_minorSection_gaussian3_of_weightZero
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 0 1 : ℝ) : ℂ)) * ((M 1 2 : ℝ) : ℂ) -
        (((M 1 0 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ)) * ((M 0 2 : ℝ) : ℂ)) * gaussian3 M)
    (y : ℝ) (hy : y ≠ 0) :
    jacquetVector3 D u₃ a₃ ((a : ℝ) * y) psiInf S 1 =
      2 * (Real.pi : ℂ) * (-Complex.I * (a : ℂ)) *
        ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ),
          ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ *
            (((y₂ ^ 2 / y₁ * (1 - (a : ℝ) * y * y₁ ^ 2)) : ℝ) : ℂ) *
            (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
            (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) := by sorry
