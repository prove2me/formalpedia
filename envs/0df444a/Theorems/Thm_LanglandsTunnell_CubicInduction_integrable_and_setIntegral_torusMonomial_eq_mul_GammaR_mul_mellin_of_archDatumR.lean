-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_and_setIntegral_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR
-- name    : LanglandsTunnell.CubicInduction.integrable_and_setIntegral_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/89ae2b1a-f0be-565d-b9ac-7abafb2ce87e
-- title:
--   Per-monomial torus integral as a^l tfrac12Γ_ℝ· Mellin transform
-- statement:
--   Let $a$ be a non-zero rational, let $P_2$ be a real archimedean parameter and let $D$ be an `ArchDatumR P₂`, that is a Whittaker function $W=D.W$ on $2\times2$ real matrices satisfying the unipotent and central transformation laws for $P_2$, smoothness, growth and zeta-integral axioms of that structure. Let $u_3\in\mathbb C$, $a_3\in\mathbb Z/2$, natural numbers $m,i,j,l$, and let $H:\mathbb R\to\mathbb C$ be given by $H(\sigma')=e^{-\pi a^2\sigma'^2}\int_0^\infty W(\mathrm{diag}(a\sigma'/w,1))\,\chi_{P_2}(w)\,|w|\,w^{\,m-u_3-1-j}\,e^{-\pi(w^{-2}+a^2w^2)}\,dw$, where $\chi_{P_2}(w)=|w|^{\,e}\cdot(\text{sign factor})$ is the central quasi-character attached to $P_2$ (exponent $u_1+u_2$ in the principal case, $2u$ in the discrete case). The assertion is that there is $\sigma_0$ such that for every $s$ with $\operatorname{Re}s>\sigma_0$: (i) the function $(y,y_1,y_2)\mapsto y^{s-2}\,\chi_{u_3+2,a_3}((y_1y_2)^{-1})\,y_2^{m+2}\,\chi_{P_2}(y_2)\,e^{-\pi(y_1^{-2}+y_2^{-2}+a^2y_2^2+a^2y^2y_1^2)}\,W(\mathrm{diag}(ayy_1/y_2,1))\,y_1^{-i}y_2^{-j}(ayy_1)^l$ is integrable for the triple product of Lebesgue measure restricted to $(0,\infty)$, where $\chi_{u,a}(y)=|y|^{u}$ times $1$ or $\operatorname{sign}y$ according as $a=0$ or not; (ii) `MellinConvergent H (s + l - 1)` holds; and (iii) the corresponding iterated integral in the order $dy_2\,dy_1\,dy$ equals $a^l\cdot\tfrac12\,\Gamma_{\mathbb R}(s+u_3+i)\cdot\mathcal M H(s+l-1)$.
--
--   This is the evaluation of a single monomial term $(1/y_1)^i(1/y_2)^j(ayy_1)^l$ of the folded archimedean torus integral of a flat section against a Whittaker datum: the $y_1$-variable produces one real Gamma factor and the remaining variables assemble into a shifted Mellin transform. It is an instance of the general real Mellin core [`LanglandsTunnell.exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin`](thm.html#LanglandsTunnell.exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin), and it is used, summed over the finitely many monomials occurring in the relevant harmonic polynomial, in the explicit computation of the archimedean zeta integral of the third Jacquet vector, the integrability conjunct licensing the interchange of the finite sum with the triple integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integrable_and_setIntegral_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR.lean

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

theorem LanglandsTunnell.CubicInduction.integrable_and_setIntegral_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR
    (a : ℚ) (ha : a ≠ 0)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (u₃ : ℂ) (a₃ : ZMod 2) (m i j l : ℕ)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ((m : ℂ) - u₃ - 1 - (j : ℂ)) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
          ((q.1 : ℝ) : ℂ) ^ (s - 2) *
            (ArchR.quasiChar (u₃ + 2) a₃ (q.2.1 * q.2.2)⁻¹ * (((q.2.2 ^ (m + 2) : ℝ)) : ℂ) * ArchR.centralChar P₂ q.2.2 *
              (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + (q.2.2 ^ 2)⁻¹ + (a : ℝ) ^ 2 * q.2.2 ^ 2 + (a : ℝ) ^ 2 * q.1 ^ 2 * q.2.1 ^ 2))) : ℂ) *
              D.W (ArchR.diagOne ((a : ℝ) * q.1 * q.2.1 / q.2.2)) *
              ((((q.2.1⁻¹) ^ i * (q.2.2⁻¹) ^ j * ((a : ℝ) * q.1 * q.2.1) ^ l : ℝ)) : ℂ)))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ))))) ∧
      MellinConvergent H (s + (l : ℂ) - 1) ∧
      ∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
          ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
            ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (m + 2) : ℝ)) : ℂ) * ArchR.centralChar P₂ y₂ *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
              D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) *
              ((((y₁⁻¹) ^ i * (y₂⁻¹) ^ j * ((a : ℝ) * y * y₁) ^ l : ℝ)) : ℂ) =
        (a : ℂ) ^ l * ((1 / 2 : ℂ) * Complex.Gammaℝ (s + u₃ + (i : ℂ)) * mellin H (s + (l : ℂ) - 1)) := by sorry
