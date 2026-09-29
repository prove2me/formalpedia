-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_integral_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
-- name    : LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_integral_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/49c20194-7380-5708-bca1-60715dbe4156
-- title:
--   Weight-zero fold of the degree-m Jacquet vector's archimedean zeta
-- statement:
--   Fix a nonzero rational $a$ and an additive character $\psi_\infty$ of the infinite adèle ring of $\mathbb{Q}$ given by $\psi_\infty(x)=\psi_{\mathrm{arch}}(ax)$ for the standard archimedean character. Let $D$ be an `ArchDatumR` for a real archimedean parameter $P_2$ (a Whittaker function $W$ on $2\times2$ real matrices, smooth off the singular locus, with the unipotent and central transformation laws, entire zeta functions, functional equation and the stated decay), and assume $W$ is right invariant under `rowIsometrySubgroup₀ ℝ`, i.e. $W(xr)=W(x)$. Let $u_3\in\mathbb{C}$, $a_3\in\mathbb{Z}/2$, let $m\ge 1$, and let $S(M)=\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^m(M_{02}+iM_{12})^m e^{-\pi\sum_{i,b}M_{ib}^2}$ on $2\times3$ real matrices. Assume $P_2=\mathrm{principal}(u_1,c,u_2,c)$ with the same sign character $c$ in both slots, and that $W(\mathrm{diagOne}(-\tau))=(-1)^{c}W(\mathrm{diagOne}(\tau))$ for $\tau\neq0$. Let $\nu_{\mathrm{mul}}$ be a Haar measure on the units of the infinite adèle ring whose image under the real coordinate is $\kappa\,|y|^{-1}dy$, let $\sigma$ be a character of the idèle units which at every real place has archimedean type $(0,e)$ in the sense of `IsArchCompAt`, and let $E$ split the infinite part of the idèles ($\mathrm{infPart}(Eu)=u$, trivial finite part). Then there is $\sigma_0$ such that for $\mathrm{Re}\,s>\sigma_0$ one has $\kappa>0$ and the zeta integral `archZeta30` of `jacquetVector3 D u₃ a₃ a psiInf S` against $\sigma\circ E$ at $s$ and $g=1$ equals $\kappa\cdot 2\pi a^m$ times the iterated integral over $y,y_1,y_2>0$ of $y^{s-2}\,\chi_{u_3+2,a_3}\bigl((y_1y_2)^{-1}\bigr)y_2^{m+2}\chi_{P_2}(y_2)\,e^{-\pi(y_1^{-2}+y_2^{-2}+a^2y_2^2+a^2y^2y_1^2)}W\bigl(\mathrm{diagOne}(ayy_1/y_2)\bigr)$ multiplied by the four-term bracket $\mathrm{He}_m(u-v-w)+(-1)^{a_3}(-1)^{c}\mathrm{He}_m(-u-v+w)+(-1)^{\bar e}(-1)^{c}\mathrm{He}_m(u-v+w)+(-1)^{\bar e}(-1)^{a_3}\mathrm{He}_m(-u-v-w)$, where $u=1/y_1$, $v=1/y_2$, $w=ayy_1$, $\bar e$ is $e$ mod $2$ and $\mathrm{He}_m(t)=\int_{\mathbb{R}}e^{-\pi u'^2}(t+iu')^m\,du'$.
--
--   This is the archimedean Rankin–Selberg (Jacquet–Piatetski-Shapiro–Shalika) zeta integral of the $GL(3)$ Whittaker vector obtained by Jacquet induction from the $GL(2)$ datum $D$, evaluated on the flat degree-$m$ Gaussian section and folded from the full matrix integral onto the positive octant with an explicit bracket of Hermite-type Gaussian moments. It is the analytic heart of the weight-zero principal-series branch, and is used by the companion statement expressing the same zeta integral as a finite sum of $\Gamma_{\mathbb{R}}$-factors times Mellin transforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_integral_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi.lean

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

theorem LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_integral_hermiteBracket_of_conjBlockHarmonic_pow_colHarmonic_gaussian3_of_weightZeroLevi
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2)
    (m : ℕ) (hm : 1 ≤ m)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m *
        ((((M 0 2 : ℝ) : ℂ) + ((1 : ℝ) : ℂ) * Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ m) * gaussian3 M)
    (u₁ u₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c u₂ c)
    (hpar : ∀ τ : ℝ, τ ≠ 0 → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      0 < κ ∧
      archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
        (κ : ℂ) * (2 * (Real.pi : ℂ) * (a : ℂ) ^ m) *
          ∫ y in Set.Ioi (0 : ℝ), ((y : ℝ) : ℂ) ^ (s - 2) *
            ∫ y₁ in Set.Ioi (0 : ℝ), ∫ y₂ in Set.Ioi (0 : ℝ),
              ArchR.quasiChar (u₃ + 2) a₃ (y₁ * y₂)⁻¹ * (((y₂ ^ (m + 2) : ℝ)) : ℂ) * ArchR.centralChar P₂ y₂ *
                (Real.exp (-(Real.pi * ((y₁ ^ 2)⁻¹ + (y₂ ^ 2)⁻¹ + (a : ℝ) ^ 2 * y₂ ^ 2 + (a : ℝ) ^ 2 * y ^ 2 * y₁ ^ 2))) : ℂ) *
                D.W (ArchR.diagOne ((a : ℝ) * y * y₁ / y₂)) *
                ((∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((1 / y₁ - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
                  (-1 : ℂ) ^ a₃.val * (-1 : ℂ) ^ c.val * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((-(1 / y₁) - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
                  (-1 : ℂ) ^ (e : ZMod 2).val * (-1 : ℂ) ^ c.val * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((1 / y₁ - 1 / y₂ + (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m) +
                  (-1 : ℂ) ^ (e : ZMod 2).val * (-1 : ℂ) ^ a₃.val * (∫ u' : ℝ, (Real.exp (-(Real.pi * u' ^ 2)) : ℂ) * (((-(1 / y₁) - 1 / y₂ - (a : ℝ) * y * y₁ : ℝ) : ℂ) + Complex.I * (u' : ℂ)) ^ m)) := by sorry
