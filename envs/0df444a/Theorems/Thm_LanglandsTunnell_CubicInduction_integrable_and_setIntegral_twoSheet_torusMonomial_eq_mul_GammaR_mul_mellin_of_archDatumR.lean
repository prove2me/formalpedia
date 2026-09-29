-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_integrable_and_setIntegral_twoSheet_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR
-- name    : LanglandsTunnell.CubicInduction.integrable_and_setIntegral_twoSheet_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/ad17fdc9-8d74-53c1-86c5-832b3ee126a9
-- title:
--   Two-sheet torus monomial: integrability and tfrac12Γ_ℝcdotM H evaluation
-- statement:
--   Let $a$ be a non-zero rational, $P_2$ a real archimedean parameter, and $D$ a real archimedean Whittaker datum for $P_2$, with Whittaker function $W=D.W$ on $2\times2$ real matrices; write $\mathrm{diag}(y)=\begin{pmatrix}y&0\\0&1\end{pmatrix}$, $\chi_{u,\alpha}(y)=|y|^{u}\cdot(1$ if $\alpha=0$, $\operatorname{sign}y$ otherwise$)$ for the real quasi-character, and $\chi_{P_2}$ for the central character of $P_2$, i.e. the quasi-character attached to its central exponent and central sign. Let $u_3\in\mathbb C$, $a_3\in\mathbb Z/2$, $n,i,j,l\in\mathbb N$, $\varepsilon=\pm1$, and let $H$ be the function $$H(\sigma')=e^{-\pi a^2\sigma'^2}\int_0^\infty\bigl(W(\mathrm{diag}(a\sigma'/w))+\varepsilon W(\mathrm{diag}(-a\sigma'/w))\bigr)\,\chi_{P_2}(w)|w|\,w^{\,n-u_3-1-j}e^{-\pi(w^{-2}+a^2w^2)}\,dw.$$ Then there is $\sigma_0\in\mathbb R$ such that for every $s$ with $\operatorname{Re}s>\sigma_0$: first, the function $$(y,y_1,y_2)\mapsto y^{s-2}\chi_{u_3+2,a_3}\bigl((y_1y_2)^{-1}\bigr)y_2^{\,n+2}\chi_{P_2}(y_2)e^{-\pi(y_1^{-2}+y_2^{-2}+a^2y_2^2+a^2y^2y_1^2)}\bigl(W(\mathrm{diag}(ayy_1/y_2))+\varepsilon W(\mathrm{diag}(-ayy_1/y_2))\bigr)y_1^{-i}y_2^{-j}(ayy_1)^l$$ is integrable for the threefold product of Lebesgue measure restricted to $(0,\infty)$; secondly, the Mellin integral of $H$ converges at $s+l-1$; and thirdly the corresponding iterated integral over $(0,\infty)^3$, taken in the order $dy_2\,dy_1\,dy$, equals $a^l\cdot\tfrac12\Gamma_{\mathbb R}(s+u_3+i)\cdot\mathcal MH(s+l-1)$.
--
--   This is the per-monomial archimedean term core, in the two-sheet variant where the Whittaker profile $\tau\mapsto W(\mathrm{diag}(\tau))$ is replaced by $W(\mathrm{diag}(\tau))+\varepsilon W(\mathrm{diag}(-\tau))$ and the column degree is $n$: one monomial $y_1^{-i}y_2^{-j}(ayy_1)^l$ of the folded torus integral is shown to converge absolutely and to factor as a single real Gamma factor times a shifted Mellin transform. It is obtained as an instance of the general real Mellin core [`LanglandsTunnell.exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin`](thm.html#LanglandsTunnell.exists_forall_integrable_and_mellinConvergent_and_setIntegral_cpow_mul_torusKernel_eq_half_GammaR_mul_mellin), and feeds the evaluation of the archimedean zeta integral of the cubic-induction Jacquet vector, where the integrability conjunct licenses interchanging the finite sum over monomials with the triple integral.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_integrable_and_setIntegral_twoSheet_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR.lean

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

theorem LanglandsTunnell.CubicInduction.integrable_and_setIntegral_twoSheet_torusMonomial_eq_mul_GammaR_mul_mellin_of_archDatumR
    (a : ℚ) (ha : a ≠ 0)
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (u₃ : ℂ) (a₃ : ZMod 2) (n i j l : ℕ) (ε : ℂ) (hε : ε = 1 ∨ ε = -1)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) + ε * D.W (ArchR.diagOne (-((a : ℝ) * (σ' / w))))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ((n : ℂ) - u₃ - 1 - (j : ℂ)) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      Integrable (fun q : ℝ × ℝ × ℝ =>
          ((q.1 : ℝ) : ℂ) ^ (s - 2) *
            (ArchR.quasiChar (u₃ + 2) a₃ (q.2.1 * q.2.2)⁻¹ * (((q.2.2 ^ (n + 2) : ℝ)) : ℂ) * ArchR.centralChar P₂ q.2.2 *
              (Real.exp (-(Real.pi * ((q.2.1 ^ 2)⁻¹ + (q.2.2 ^ 2)⁻¹ + (a : ℝ) ^ 2 * q.2.2 ^ 2 + (a : ℝ) ^ 2 * q.1 ^ 2 * q.2.1 ^ 2))) : ℂ) *
              (D.W (ArchR.diagOne ((a : ℝ) * q.1 * q.2.1 / q.2.2)) + ε * D.W (ArchR.diagOne (-((a : ℝ) * q.1 * q.2.1 / q.2.2)))) *
              ((((q.2.1⁻¹) ^ i * (q.2.2⁻¹) ^ j * ((a : ℝ) * q.1 * q.2.1) ^ l : ℝ)) : ℂ)))
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod ((volume.restrict (Set.Ioi (0 : ℝ))).prod (volume.restrict (Set.Ioi (0 : ℝ))))) ∧
      MellinConvergent H (s + (l : ℂ) - 1) ∧
      ∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
          ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
            ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (n + 2) : ℝ)) : ℂ) * ArchR.centralChar P₂ y₂ *
              (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
              (D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) + ε * D.W (ArchR.diagOne (-((a : ℝ) * y * y₁ / y₂)))) *
              ((((y₁⁻¹) ^ i * (y₂⁻¹) ^ j * ((a : ℝ) * y * y₁) ^ l : ℝ)) : ℂ) =
        (a : ℂ) ^ l * ((1 / 2 : ℂ) * Complex.Gammaℝ (s + u₃ + (i : ℂ)) * mellin H (s + (l : ℂ) - 1)) := by sorry
