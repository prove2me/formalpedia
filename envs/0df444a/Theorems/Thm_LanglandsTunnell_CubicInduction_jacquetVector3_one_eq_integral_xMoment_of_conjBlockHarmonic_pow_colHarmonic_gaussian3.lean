-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/dc9d2f52-2131-559d-9206-9f621ba37f71
-- title:
--   Torus unfolding of the degree-m Jacquet vector with x-moment
-- statement:
--   Let $a$ be a nonzero rational number and let $\psi_\infty$ be an additive character of the infinite adele ring of $\mathbb{Q}$ which is the standard archimedean character composed with multiplication by the image of $a$, i.e. $\psi_\infty(x)=\psi_{\mathrm{arch}}(a\,x)$. Let $D$ be an archimedean Whittaker datum `ArchDatumR` for a real archimedean parameter $P_2$, so that $D.W$ is a smooth function on $2\times 2$ real matrices transforming by $W(\mathrm{unip}(x)g)=e^{2\pi i x}W(g)$ under unipotents and by the central quasi-character of $P_2$ under scalars, with the usual zeta-integral, functional-equation and decay properties; assume in addition that $D.W$ has weight $k_0\in\mathbb{N}$ under right translation by the subgroup `rowIsometrySubgroup₀ ℝ` of $\mathrm{GL}_2(\mathbb{R})$, i.e. $D.W(x r)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\,D.W(x)$. Let $m,n\in\mathbb{N}$ and $\varepsilon'\in\mathbb{R}$ satisfy either $\varepsilon'=-1$ and $n=k_0-m$, or $\varepsilon'=1$ and $n=m-k_0$ (as integers). Let $u_3\in\mathbb{C}$, $a_3\in\mathbb{Z}/2$, and let the Schwartz section $S$ on $2\times 3$ real matrices be $$S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^m\,(M_{02}+\varepsilon' i M_{12})^n\,e^{-\pi\sum_{i,b}M_{ib}^2}.$$ Then for every nonzero real $y$, the Jacquet vector $\mathrm{jacquetVector3}\,D\,u_3\,a_3\,(ay)\,\psi_\infty\,S$ evaluated at the identity of $\mathrm{GL}_3$ equals $$2\pi(\varepsilon' a)^n\int_{\mathbb{R}}\int_{y_2>0}\chi_{u_3+2,a_3}\bigl((y_1y_2)^{-1}\bigr)\frac{y_2^{\,n+1}}{|y_1|}e^{-\pi(y_1^{-2}+y_2^{-2}+a^2y_2^2)}\,\chi_{P_2}(y_2)|y_2|\,D.W\!\left(\begin{smallmatrix}ayy_1/y_2&0\\0&1\end{smallmatrix}\right)\left[\int_{\mathbb{R}}e^{-\pi x^2/y_1^2}\Bigl(\tfrac1{y_1}-\tfrac1{y_2}+\tfrac{i x}{y_1}\Bigr)^m e^{2\pi i a y x}\,dx\right]dy_2\,dy_1,$$ where $\chi_{u,a}(t)=|t|^{u}$ times $\mathrm{sign}(t)$ when $a\neq0$, and $\chi_{P_2}$ is the central quasi-character of $P_2$.
--
--   This is the Iwasawa (torus) unfolding of the Jacquet–Whittaker integral attached to the degree-$m$ conjugate-block harmonic flat section with $\theta$-matched column factor: the $4$-dimensional matrix integral defining the vector is reduced to a double integral over the Iwasawa half-plane against the torus profile $y\mapsto D.W(\mathrm{diag}(y,1))$, with the whole $x$-dependence kept as a one-dimensional Gaussian moment of degree $m$. It is the analytic input to the two statements producing a nonvanishing archimedean zeta value for such sections.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3.lean

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

theorem LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_xMoment_of_conjBlockHarmonic_pow_colHarmonic_gaussian3
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (k₀ : ℕ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ (k₀ : ℤ) r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (m n : ℕ) (ε' : ℝ) (hcol : (ε' = -1 ∧ (n : ℤ) = (k₀ : ℤ) - m) ∨ (ε' = 1 ∧ (n : ℤ) = (m : ℤ) - k₀))
    (u₃ : ℂ) (a₃ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + (ε' : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (y : ℝ) (hy : y ≠ 0) :
    jacquetVector3 D u₃ a₃ ((a : ℝ) * y) psiInf S 1 =
      2 * (Real.pi : ℂ) * ((ε' : ℂ) * (a : ℂ)) ^ n *
        ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ),
          ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ *
            (((y₂ ^ (n + 1) / |y₁| : ℝ)) : ℂ) *
            (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2))) : ℂ) *
            (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) *
            (∫ x : ℝ, (Real.exp (-(Real.pi * (x ^ 2 / y₁ ^ 2))) : ℂ) *
              ((((1 / y₁ - 1 / y₂ : ℝ) : ℂ)) + (Complex.I * (((1 / y₁ : ℝ)) : ℂ)) * (x : ℂ)) ^ m *
              ArchR.psi ((a : ℝ) * y * x)) := by sorry
