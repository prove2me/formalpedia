-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_conjBlockHarmonicOne_colHarmonic_gaussian3
-- name    : LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_conjBlockHarmonicOne_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/a531da29-1dde-5a7c-a7be-2db1ee558d58
-- title:
--   Archimedean zeta of the block-harmonic Jacquet vector as a Mellin transform
-- statement:
--   Fix a nonzero rational $a$ and an additive character $\psi_\infty$ of the infinite adele ring of $\mathbb{Q}$ with values in $\mathbb{C}$ which is the standard archimedean character `psiArch` precomposed with multiplication by the image of $a$. Let $D$ be an archimedean Whittaker datum `ArchDatumR` for a real archimedean parameter $P_2$, with Whittaker function $W = D.W$ on $2\times 2$ real matrices, and let $k_0 \ge 1$ be an integer such that $W(x r) = \mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\, W(x)$ for all $r$ in `rowIsometrySubgroup₀ ℝ` and all $x \in \mathrm{GL}_2(\mathbb{R})$; let $n$ be the natural number with $n = k_0 - 1$. Fix $u_3 \in \mathbb{C}$, $a_3 \in \mathbb{Z}/2$, and let $S$ be the section on $2\times 3$ real matrices $M \mapsto \bigl((M_{00} - i M_{10}) - i (M_{01} - i M_{11})\bigr)(M_{02} - i M_{12})^n \exp(-\pi\sum_{i,b} M_{ib}^2)$. Let $\nu^\times$ be a Haar measure on the units of the infinite adele ring whose push-forward along the real coordinate is $\kappa$ times $|y|^{-1}\,dy$; let $\sigma$ be a character of the idele group whose archimedean component at every real place is $x \mapsto (x/|x|)^{e}$ with $e \equiv a_3 + 1 \pmod 2$, and let $E$ be a monoid homomorphism splitting the infinite part, so that $E(u)$ has infinite part $u$ and trivial finite part. Put $$H(\sigma') = e^{-\pi a^2 \sigma'^2}\int_0^\infty \Bigl(W\bigl(\mathrm{diag}(a\sigma'/w,1)\bigr) - (-1)^{a_3} W\bigl(\mathrm{diag}(-a\sigma'/w,1)\bigr)\Bigr)\,\omega_{P_2}(w)|w|\, w^{\,n-u_3-1} e^{-\pi(w^{-2}+a^2w^2)}\,dw,$$ where $\omega_{P_2}$ is the central quasicharacter `ArchR.centralChar` of $P_2$. Then there is a real $\sigma_0$ such that for every $s$ with $\mathrm{Re}\,s > \sigma_0$ the Mellin integral of $H$ converges at $s-1$ and the archimedean zeta integral `archZeta30` of the Jacquet vector `jacquetVector3 D u₃ a₃ a psiInf S`, taken against $\sigma \circ E$ at the identity of $\mathrm{GL}_3$, equals $\kappa \cdot 2\pi(-a)^n \cdot \Gamma_{\mathbb{R}}(s+u_3+1)\cdot \mathcal{M}H(s-1)$.
--
--   This is the archimedean local computation in the cubic induction: it evaluates the $\mathrm{GL}_3$ zeta integral $\int W(\mathrm{diag}(a,1,1)g)\sigma(a)\|a\|^{s-1}$ of the Jacquet vector attached to the conjugate block-harmonic Gaussian section as an explicit $\Gamma_{\mathbb{R}}$-factor times the Mellin transform of the torus profile $H$. It is used to produce an admissible twist for which this zeta integral is nonvanishing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_conjBlockHarmonicOne_colHarmonic_gaussian3.lean

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

theorem LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_conjBlockHarmonicOne_colHarmonic_gaussian3
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
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ ((n : ℂ) - u₃ - 1) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent H (s - 1) ∧
        archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
          (κ : ℂ) * (2 * (Real.pi : ℂ) * (-(a : ℂ)) ^ n) * Complex.Gammaℝ (s + u₃ + 1) * mellin H (s - 1) := by sorry
