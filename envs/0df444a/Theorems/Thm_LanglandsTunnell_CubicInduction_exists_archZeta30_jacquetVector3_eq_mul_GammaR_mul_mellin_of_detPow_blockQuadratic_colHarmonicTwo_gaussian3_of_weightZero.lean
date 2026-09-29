-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero
-- name    : LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/e1461991-dad7-5446-9564-7cf11edec312
-- title:
--   Archimedean GL₃× GL₁ zeta integral as a Mellin transform
-- statement:
--   Let $a\in\mathbb{Q}$ be nonzero and let $\psi_\infty$ be an additive character of the infinite adeles of $\mathbb{Q}$ with $\psi_\infty(x)=\mathrm{psiArch}(a\,x)$. Let $D$ be an archimedean Whittaker datum `ArchDatumR` for a real parameter $P_2$, whose function $W=D.W$ on $M_2(\mathbb{R})$ is assumed right invariant under the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$. Fix $u_3\in\mathbb{C}$, $a_3\in\mathbb{Z}/2$, $\delta\in\{0,1\}$ and the section $S(M)=(M_{00}M_{11}-M_{01}M_{10})^{\delta}\bigl((M_{00}+iM_{10})^2+(M_{01}+iM_{11})^2\bigr)(M_{02}-iM_{12})^2\exp\bigl(-\pi\sum_{i,b}M_{ib}^2\bigr)$ on $2\times 3$ real matrices. Assume $P_2=\mathrm{principal}(u_1,c,u_2,c)$, the parity law $W(\mathrm{diag}(-\tau,1))=(-1)^{c}W(\mathrm{diag}(\tau,1))$ for $\tau\neq0$, and $\delta\equiv a_3+c+1 \pmod 2$. Let $\nu^\times$ be a Haar measure on the ideles at infinity whose image under the real coordinate is $\kappa\,dy/|y|$, let $\sigma$ be a character of the idele group whose local component at each real place is $x\mapsto \|x\|^{0}(\mathrm{sgn}\,x)^{e}$ with $e\equiv a_3+\delta\pmod 2$, and let $E$ split the archimedean ideles into the ideles, with trivial finite part. Put $H(\sigma')=e^{-\pi a^2\sigma'^2}\int_0^\infty W(\mathrm{diag}(a\sigma'/w,1))\,\omega_{P_2}(w)|w|\,w^{-u_3-\delta}e^{-\pi(w^{-2}+a^2w^2)}\,dw$, with $\omega_{P_2}$ the central quasicharacter of $P_2$. Then there is $\sigma_0\in\mathbb{R}$ such that for all $s$ with $\mathrm{Re}\,s>\sigma_0$ the Mellin transform of $H$ converges at $s$ and the zeta integral $\int (\mathrm{jacquetVector3}\,D\,u_3\,a_3\,a\,\psi_\infty\,S)(\iota(\mathrm{diag}(z,1)))\,\sigma(E z)\,\|z\|^{s-1}\,d\nu^\times(z)$ equals $\kappa\cdot 8\pi a^3\cdot\Gamma_{\mathbb{R}}(s+u_3+\delta)\cdot \mathcal{M}H(s)$.
--
--   This is the archimedean computation of the $GL_3\times GL_1$ zeta integral attached to the Jacquet vector built from the explicit quadratic-times-Gaussian section, identifying it with a gamma factor times the Mellin transform of a one-variable profile $H$ built from the torus restriction of $W$. It is used to prove that a suitable twist makes this zeta integral nonvanishing, a hypothesis of the converse theorem in the cubic-induction step of Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero.lean

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

theorem LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_detPow_blockQuadratic_colHarmonicTwo_gaussian3_of_weightZero
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2) (δ : ℕ) (hδ : δ = 0 ∨ δ = 1)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) ^ 2 + (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ)) ^ 2) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 2) * gaussian3 M)
    (u₁ u₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c u₂ c)
    (hpar : ∀ τ : ℝ, τ ≠ 0 → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (hodd : ((δ : ℕ) : ZMod 2) = a₃ + c + 1)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e)
    (he : ((e : ZMod 2)) = a₃ + ((δ : ℕ) : ZMod 2))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ (-u₃ - (δ : ℂ)) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent H s ∧
        archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
          (κ : ℂ) * (8 * (Real.pi : ℂ) * (a : ℂ) ^ 3) * Complex.Gammaℝ (s + u₃ + (δ : ℂ)) * mellin H s := by sorry
