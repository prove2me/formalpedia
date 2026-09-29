-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_blockHarmonicOne_colHarmonic_gaussian3_of_weightZero
-- name    : LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_blockHarmonicOne_colHarmonic_gaussian3_of_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/f4fb84ca-2959-5795-91f9-a288f442a10c
-- title:
--   Archimedean zeta of the weight-zero Jacquet vector as Γ_ℝ times a Mellin transform
-- statement:
--   Fix a nonzero rational $a$ and an additive character $\psi_\infty$ of the infinite adele ring of $\mathbb Q$ of the form $\psi_\infty(x)=\psi_{\mathrm{arch}}(ax)$. Let $D$ be an archimedean Whittaker datum for a real parameter $P_2$ (so $D.W$ on $2\times2$ real matrices satisfies the unipotent and central transformation laws, has entire zeta integrals with functional equation and the stated growth and decay bounds), and assume $D.W$ is invariant under right translation by `rowIsometrySubgroup₀ ℝ`. Let $u_3\in\mathbb C$, $a_3\in\mathbb Z/2$, and let $S$ be the explicit Schwartz section $M\mapsto\bigl((M_{00}+iM_{10})-i(M_{01}+iM_{11})\bigr)(M_{02}-iM_{12})\exp(-\pi\sum_{i,b}M_{ib}^2)$ on $2\times3$ real matrices. Assume $P_2=\mathrm{principal}(u_1,c,u_2,c)$, that $D.W(\mathrm{diag}(-\tau,1))=(-1)^{c}D.W(\mathrm{diag}(\tau,1))$ for $\tau\neq0$, and $a_3=c$. Let $\nu^\times$ be a Haar measure on the units of the infinite adele ring whose push-forward under the real coordinate is $\kappa\,|y|^{-1}dy$, let $\sigma$ be a character of the idele units whose archimedean component at every real place is $x\mapsto(x/|x|)^{e}$ with $e\equiv a_3\pmod 2$, and let $E$ be a homomorphism splitting the idele units over the infinite part (infinite part $u$, finite part $1$). Put $H(\sigma')=e^{-\pi a^2\sigma'^2}\int_0^\infty D.W(\mathrm{diag}(a\sigma'/w,1))\,|w|^{u_1+u_2}|w|\,w^{-u_3-1}e^{-\pi(w^{-2}+a^2w^2)}\,dw$. Then there is $\sigma_0\in\mathbb R$ such that for all $s$ with $\operatorname{Re}s>\sigma_0$ the Mellin transform of $H$ converges at $s-1$ and the archimedean zeta integral $\int W(\iota(\mathrm{diag}(z,1)))\,\sigma(E z)\,\|z\|^{s-1}\,d\nu^\times(z)$, taken at the identity with $W$ the Jacquet vector $g\mapsto\mathrm{quasiChar}_{u_3+1,a_3}(\det g_\infty)\int_{M_2(\mathbb R)}\mathrm{godementInner3}(\psi_\infty,S)(e,g_\infty)\,\mathrm{quasiChar}_{u_3+2,a_3}(\det e)\,|\det e|^{-2}D.W(\mathrm{diag}(a,1)e^{-1})\,de$, equals $\kappa\cdot 4\pi(-a)\cdot\Gamma_{\mathbb R}(s+u_3)\cdot\mathcal M H(s-1)$.
--
--   This is the archimedean zeta computation for the distinguished ("major") Godement section in the converse-theorem input to the Langlands–Tunnell argument: it identifies the $\mathrm{GL}_3$ archimedean zeta integral of the weight-zero Jacquet vector with a $\Gamma_{\mathbb R}$-factor times the Mellin transform of an explicit torus profile. It is used by the subsequent nonvanishing statement, which produces an admissible twist for which this zeta integral is nonzero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_blockHarmonicOne_colHarmonic_gaussian3_of_weightZero.lean

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

theorem LanglandsTunnell.CubicInduction.exists_archZeta30_jacquetVector3_eq_mul_GammaR_mul_mellin_of_blockHarmonicOne_colHarmonic_gaussian3_of_weightZero
    (a : ℚ) (ha : a ≠ 0)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (u₃ : ℂ) (a₃ : ZMod 2)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M =>
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ))) *
        ((((M 0 2 : ℝ) : ℂ) - Complex.I * ((M 1 2 : ℝ) : ℂ)) ^ 1) * gaussian3 M)
    (u₁ u₂ : ℂ) (c : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c u₂ c)
    (hpar : ∀ τ : ℝ, τ ≠ 0 → D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (heven : a₃ = c)
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (κ : ℝ)
    (hκ : MeasureTheory.Measure.map
        (fun z : (InfiniteAdeleRing ℚ)ˣ => StandardKernel.realCoord (z : InfiniteAdeleRing ℚ)) ν_mul =
      ENNReal.ofReal κ • (MeasureTheory.volume : MeasureTheory.Measure ℝ).withDensity
        fun y => ENNReal.ofReal |y|⁻¹)
    (σ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (e : ℤ)
    (hσ : ∀ v : InfinitePlace ℚ, v.IsReal → IsArchCompAt ℚ σ v 0 e)
    (he : ((e : ZMod 2)) = a₃)
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (H : ℝ → ℂ)
    (hH : H = fun σ' => (Real.exp (-(Real.pi * (a : ℝ) ^ 2 * σ' ^ 2)) : ℂ) *
        ∫ w in Set.Ioi (0 : ℝ),
          D.W (ArchR.diagOne ((a : ℝ) * (σ' / w))) *
            (ArchR.centralChar P₂ w * ((|w| : ℝ) : ℂ)) * ((w : ℝ) : ℂ) ^ (-u₃ - 1) *
            (Real.exp (-(Real.pi * ((w ^ 2)⁻¹ + (a : ℝ) ^ 2 * w ^ 2))) : ℂ)) :
    ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re →
      MellinConvergent H (s - 1) ∧
        archZeta30 ν_mul (jacquetVector3 D u₃ a₃ (a : ℝ) psiInf S) (σ.comp E) s 1 =
          (κ : ℂ) * (4 * (Real.pi : ℂ) * (-(a : ℂ))) * Complex.Gammaℝ (s + u₃) * mellin H (s - 1) := by sorry
