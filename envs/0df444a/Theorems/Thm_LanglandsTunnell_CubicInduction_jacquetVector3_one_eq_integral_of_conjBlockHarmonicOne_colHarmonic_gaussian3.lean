-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_conjBlockHarmonicOne_colHarmonic_gaussian3
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_of_conjBlockHarmonicOne_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/8ee06025-362f-57c6-b48d-4253fd740329
-- title:
--   Jacquet vector at 1 of a conjugate block-harmonic Gaussian section
-- statement:
--   Fix a nonzero rational $a$ and an additive character $\psi_\infty$ of the infinite adele ring of $\mathbb{Q}$ valued in $\mathbb{C}$ which is the standard archimedean character composed with multiplication by $a$, i.e. $\psi_\infty(x) = \mathrm{psiArch}(a x)$ for all $x$. Let $P_2$ be a real archimedean parameter (principal or discrete), $D$ an archimedean $GL_2$-datum of parameter $P_2$ — so $D.W$ is a function on $2\times 2$ real matrices with the smoothness, unipotent and central transformation laws, zeta-integral, functional-equation, finite-order and decay properties of `ArchDatumR` — and let $k_0 \in \mathbb{Z}$ be such that $D.W$ satisfies the weight law $D.W(x r) = \mathrm{archWeightChar}\mathbb{R}\, k_0(r)\cdot D.W(x)$ for all $x \in GL_2(\mathbb{R})$ and all $r$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$, with $k_0 \ge 1$, and let $n \in \mathbb{N}$ satisfy $n = k_0 - 1$. Let $u_3 \in \mathbb{C}$, $a_3 \in \mathbb{Z}/2$, and let $S$ on $2\times 3$ real matrices be the section
--   $$S(M) = \bigl((M_{00} - iM_{10}) - i(M_{01} - iM_{11})\bigr)\,(M_{02} - iM_{12})^{n}\,e^{-\pi\sum_{i,b}M_{ib}^{2}},$$
--   the last factor being `gaussian3`. Then for every nonzero real $y$, the value at the identity of the Jacquet vector $\mathrm{jacquetVector3}\,D\,u_3\,a_3\,(ay)\,\psi_\infty\,S$ — that is, $\chi_{u_3+1,a_3}(\det)$ times the integral over $e \in M_2(\mathbb{R})$ of `jacquetIntegrand3`, evaluated at $g = 1$ — equals
--   $$2\pi(-a)^{n}\int_{\mathbb{R}}\int_{0}^{\infty}\chi_{u_3+2,a_3}\bigl((y_1y_2)^{-1}\bigr)\,y_2^{\,n+1}\Bigl(\tfrac1{y_1} - \tfrac1{y_2} - a y y_1\Bigr)e^{-\pi(y_1^{-2}+y_2^{-2}+a^2y_2^2+a^2y^2y_1^2)}\,\omega_{P_2}(y_2)|y_2|\;D.W\!\begin{pmatrix}a y y_1/y_2&0\\0&1\end{pmatrix}dy_2\,dy_1,$$
--   where $\chi_{u,\varepsilon}(t) = |t|^{u}$ times $1$ or $\mathrm{sign}(t)$ according as $\varepsilon = 0$ or not, $\omega_{P_2}$ is the central quasi-character $\chi$ attached to the central exponent and sign of $P_2$, and the matrix argument is `ArchR.diagOne`.
--
--   This is the archimedean computation, in the Godement–Jacquet style, of the local Jacquet (Whittaker) vector attached to a Gaussian Schwartz section on $2\times 3$ matrices whose polynomial part is a conjugate block factor times the $n$-th power of a harmonic column factor, the exponent $n = k_0-1$ being matched to the $SO(2)$-weight of the datum $D$ so that the angular integration survives. It feeds the Mellin-transform and $\Gamma$-factor identification used to show non-vanishing of the associated archimedean zeta integral in the converse-theorem step of the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_one_eq_integral_of_conjBlockHarmonicOne_colHarmonic_gaussian3.lean

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

theorem LanglandsTunnell.CubicInduction.jacquetVector3_one_eq_integral_of_conjBlockHarmonicOne_colHarmonic_gaussian3
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hk₀ : 1 ≤ k₀) (n : ℕ) (hn : (n : ℤ) = k₀ - 1)
    (u₃ : ℂ) (a₃ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ n) * gaussian3 M)
    (y : ℝ) (hy : y ≠ 0) :
    jacquetVector3 D u₃ a₃ ((a : ℝ) * y) psiInf S 1 =
      2 * (Real.pi : ℂ) * (-(a : ℂ)) ^ n *
        ∫ y₁ : ℝ, ∫ y₂ in Set.Ioi (0 : ℝ),
          ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ *
            (((y₂ ^ (n + 1) * (y₁⁻¹ - y₂⁻¹ - (a : ℝ) * y * y₁)) : ℝ) : ℂ) *
            (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
            (ArchR.centralChar P₂ y₂ * ((|y₂| : ℝ) : ℂ)) *
            D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) := by sorry
