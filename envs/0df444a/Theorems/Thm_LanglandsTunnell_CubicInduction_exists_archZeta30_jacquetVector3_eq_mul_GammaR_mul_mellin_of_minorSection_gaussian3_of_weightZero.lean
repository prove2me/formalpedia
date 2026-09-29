-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero
-- name    : LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/2e07ba71-a1aa-5b3f-8a7f-b28cf9524357
-- title:
--   Archimedean zeta of the minor-section Jacquet vector as Mellin transform
-- statement:
--   Fix a nonzero $a \in \mathbb{Q}$ and an additive character $\psi_\infty$ of the infinite adele ring of $\mathbb{Q}$ with $\psi_\infty(x) = \mathrm{psiArch}(a x)$ for all $x$. Let $D$ be an archimedean Whittaker datum `ArchDatumR P₂` for a real parameter $P_2$, whose function $D.W$ on $2\times 2$ real matrices is assumed right invariant under the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$, and fix $u_3 \in \mathbb{C}$, $a_3 \in \mathbb{Z}/2$. Let $S$ be the section $S(M) = \big((M_{00} - iM_{01})M_{12} - (M_{10} - iM_{11})M_{02}\big)\,e^{-\pi \sum_{i,b} M_{ib}^2}$ on $2 \times 3$ real matrices. Let $\nu^\times$ be a Haar measure on the units of the infinite adele ring whose push-forward under the real coordinate `realCoord` is $\kappa \cdot |y|^{-1}\,dy$, let $\sigma$ be a homomorphism from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$ whose component at every real infinite place $v$ satisfies `IsArchCompAt` with exponent $0$ and integer $e$, that is $\mathrm{archLocalChar}(\sigma,v)(x) = (x/\|x\|)^e$, with $e \equiv a_3 + 1 \pmod 2$, and let $E$ be a monoid homomorphism from the units of the infinite adeles to the ideles with infinite part the identity and trivial finite part. Finally let $$H(\sigma') = e^{-\pi a^2 \sigma'^2} \int_0^\infty \Big(D.W\big(\mathrm{diagOne}(a\sigma'/w)\big) - (-1)^{a_3} D.W\big(\mathrm{diagOne}(-a\sigma'/w)\big)\Big)\,\omega_{P_2}(w)\,|w|\,w^{-u_3}\, e^{-\pi(w^{-2} + a^2 w^2)}\,dw,$$ with $\mathrm{diagOne}(y) = \mathrm{diag}(y,1)$ and $\omega_{P_2} =$ `ArchR.centralChar P₂`. The assertion is that there is $\sigma_0 \in \mathbb{R}$ such that for every $s$ with $\mathrm{Re}\,s > \sigma_0$ the Mellin transform of $H$ converges at $s-1$ and the zeta integral $$\mathrm{archZeta30}\big(\nu^\times, \mathrm{jacquetVector3}(D,u_3,a_3,a,\psi_\infty,S), \sigma \circ E\big)(s,1) = \int \mathrm{jacquetVector3}(\iota(\mathrm{diag}(z,1)))\,\sigma(E z)\,\|z\|^{s-1}\,d\nu^\times(z)$$ equals $\kappa \cdot 2\pi(-ia) \cdot \Gamma_{\mathbb{R}}(s + u_3 + 1) \cdot \mathcal{M}H(s-1)$.
--
--   This is the archimedean $GL_3 \times GL_1$ zeta computation for the Jacquet vector attached to the minor (weight-zero) Schwartz section, identifying it on a right half-plane with a $\Gamma_{\mathbb{R}}$-factor times the Mellin transform of an explicit torus profile $H$. It feeds the non-vanishing statement `exists_isAdmissibleTwist_archZeta30_jacquetVector3_ne_zero_of_minorSection_gaussian3`, where vanishing of the zeta integral on a half-plane is converted, via uniqueness for Mellin transforms, into vanishing of $H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero.lean

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

open NumberField AutomorphicForm LanglandsTunnell.Converse LanglandsTunnell
open LanglandsTunnell.CubicInduction
open MeasureTheory

theorem LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_minorSection_gaussian3_of_weightZero
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
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e)
    (he : ((e : ZMod 2)) = a₃ + 1)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          (D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) - (-1 : ℂ) ^ a₃.val * D.W (ArchR.diagOne (-((a : ℝ) * (σ' / w))))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ (-u₃) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent H (s - 1) ∧
        archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
          (κ : ℂ) * (2 * (Real.pi : ℂ) * (-Complex.I * (a : ℂ))) * Complex.Gammaℝ (s + u₃ + 1) * mellin H (s - 1) := by sorry
