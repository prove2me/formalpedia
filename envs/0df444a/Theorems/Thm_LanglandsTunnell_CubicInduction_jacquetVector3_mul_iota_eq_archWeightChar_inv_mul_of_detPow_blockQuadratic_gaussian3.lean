-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_mul_iota_eq_archWeightChar_inv_mul_of_detPow_blockQuadratic_gaussian3
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_mul_iota_eq_archWeightChar_inv_mul_of_detPow_blockQuadratic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/9f3155e5-1764-52ad-91cc-2ab834268bcf
-- title:
--   Weight zero of the block-quadratic Gaussian Jacquet vector
-- statement:
--   Let $K$ be a number field with $[K:\mathbb Q]=3$ and let $\mu$ be a character of the idele units of $K$ which is trivial on $K^\times$, continuous and unitary. Let data $uR(w)\in\mathbb C$, $aR(w)\in\mathbb Z/2$ at the real places and $uC(w)\in\mathbb C$, $kC(w)\in\mathbb Z$ at the complex places be such that the archimedean local component of $\mu$ at $w$ is $x\mapsto \|x\|^{\mathrm{mult}(w)\,u}\,(x/\|x\|)^{a}$ with the corresponding exponents, and let $\omega$ be a character of the idele units of $\mathbb Q$ whose component at the real place has exponents $\sum_w uR(w)+\sum_w 2\,uC(w)$ and $\sum_w aR(w)+\sum_w(kC(w)+1)$. Further standing data: a splitting $E$ of the infinite ideles with trivial finite part, a nonzero $a\in\mathbb Q$ with a unit $a_\infty$ above it, the additive character $\psi_\infty(x)=\psi_{\mathrm{arch}}(ax)$, Borel measurable structures on the infinite adeles and their units, the scaled additive measure $\nu_{\mathrm{add}}=|a|^{1/2}\cdot$(transported Lebesgue measure) and a Haar measure $\nu_{\mathrm{mul}}$. Fix a real place $w_0$ of $K$ and a parameter $P_2$ which, according as $K$ has three real places $w_0,w_1,w_2$ or one real place $w_0$ and one complex place $w_C$, is the principal parameter $(uR(w_1),aR(w_1),uR(w_2),aR(w_2))$, or else the discrete parameter $(uC(w_C),|kC(w_C)|)$ when $kC(w_C)\neq0$ and the principal parameter $(uC(w_C),0,uC(w_C),1)$ when $kC(w_C)=0$. Let $D$ be an archimedean Whittaker datum of type $P_2$ (a function $W$ on $2\times 2$ real matrices, smooth on the invertible locus, with the unipotent and central transformation laws, an entire zeta function satisfying the functional equation with the $\Gamma$- and $\varepsilon$-factors of $P_2$, of finite order, together with the decay bounds). Let $p:\mathbb R\to\mathbb R\to\mathbb C$ be arbitrary, $\delta\in\mathbb N$, and let the section $S$ on $2\times3$ real matrices be
--   $$S(M)=p(M_{02},M_{12})\,(M_{00}M_{11}-M_{01}M_{10})^{\delta}\,\bigl((M_{00}+iM_{10})^2+(M_{01}+iM_{11})^2\bigr)\,e^{-\pi\sum_{i,b}M_{ib}^2}.$$
--   Then for every $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb R)$ and every $g\in GL_3$ of the infinite adeles of $\mathbb Q$, the Jacquet vector `jacquetVector3` attached to $D$, to the exponents $uR(w_0),aR(w_0)$, to $a$, to $\psi_\infty$ and to $S$ satisfies
--   $$J\bigl(g\cdot \mathrm{arch}(\iota(\kappa))\bigr)=\bigl(\verb|archWeightCharℝ|\,0\,\kappa\bigr)^{-1}\,J(g),$$
--   where $\mathrm{arch}(\iota(\kappa))$ denotes the archimedean component of the image of $\kappa$ under the embedding of $GL_2$ at the real place of $\mathbb Q$ into $GL_2$ of the adeles followed by the upper-left block embedding into $GL_3$. Here $J(g)$ is $\mathrm{quasiChar}(uR(w_0)+1,aR(w_0))(\det g_\infty)$ times the integral over $2\times2$ real matrices $e$ of the Godement inner product of $S$ at $(e,g_\infty)$ against $\psi_\infty$, weighted by $\mathrm{quasiChar}(uR(w_0)+2,aR(w_0))(\det e)\,|\det e|^{-2}\,W(\mathrm{diag}(a,1)\,e^{-1})$.
--
--   This is the $K$-type computation for this particular section: the Jacquet vector built from a determinant power times the block quadratic $(M_{00}+iM_{10})^2+(M_{01}+iM_{11})^2$ times the Gaussian transforms under right translation by the embedded rotation subgroup by the inverse of the weight-$0$ archimedean character, i.e. it is invariant. It supplies the weight clause of the archimedean Rankin–Selberg row [`LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_not_weightOne`](thm.html#LanglandsTunnell.RankinSelberg.exists_mem_polyGauss3_iotaWeight_archZeta30_ne_zero_unfoldedTorusPair_and_dualTorusPair_eq_gammaFactor_of_archWhittakerDatum_of_isCasimirEigen_of_not_weightOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_mul_iota_eq_archWeightChar_inv_mul_of_detPow_blockQuadratic_gaussian3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant
import Definitions.Def_LanglandsTunnell_CubicLambda
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchZeta31
import Definitions.Def_LanglandsTunnell_HeckeTate
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_LanglandsTunnell_ArchBaseChange
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse
open NumberField.TateGlobal NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace.Completion
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction LanglandsTunnell.CubicLambda MeasureTheory
open scoped nonZeroDivisors
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open scoped Classical in

theorem LanglandsTunnell.CubicInduction.jacquetVector3_mul_iota_eq_archWeightChar_inv_mul_of_detPow_blockQuadratic_gaussian3
    (K : Type) [Field K] [NumberField K]
    (hdeg : Module.finrank ℚ K = 3)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (hμ : IsAdmissibleTwist K μ)
    (uR : ∀ w : InfinitePlace K, w.IsReal → ℂ) (aR : ∀ w : InfinitePlace K, w.IsReal → ZMod 2)
    (uC : ∀ w : InfinitePlace K, w.IsComplex → ℂ) (kC : ∀ w : InfinitePlace K, w.IsComplex → ℤ)
    (huR : ∀ w, ∀ hw : w.IsReal, IsArchCompAt K μ w (uR w hw) ((aR w hw).val : ℤ))
    (huC : ∀ w, ∀ hw : w.IsComplex, IsArchCompAt K μ w (uC w hw) (kC w hw))
    (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ)
    (hω : ∀ v : InfinitePlace ℚ, v.IsReal →
      IsArchCompAt ℚ ω v
        ((∑ᶠ (w) (hw : w.IsReal), uR w hw) + (∑ᶠ (w) (hw : w.IsComplex), 2 * uC w hw))
        ((∑ᶠ (w) (hw : w.IsReal), ((aR w hw).val : ℤ)) + (∑ᶠ (w) (hw : w.IsComplex), (kC w hw + 1))))
    (E : (InfiniteAdeleRing ℚ)ˣ →* (AdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hE : ∀ u : (InfiniteAdeleRing ℚ)ˣ,
      M4aHerbrand.infPart (E u) = u ∧ RatIdele.finPart (E u) = 1)
    (a : ℚ) (aInf : (InfiniteAdeleRing ℚ)ˣ)
    (haInf : (aInf : InfiniteAdeleRing ℚ) = algebraMap ℚ (InfiniteAdeleRing ℚ) a)
    (psiInf : AddChar (InfiniteAdeleRing ℚ) ℂ)
    (hpsiInf : ∀ x : InfiniteAdeleRing ℚ,
      psiInf x = NumberField.StandardAddChar.psiArch (algebraMap ℚ (InfiniteAdeleRing ℚ) a * x))
    [mA : MeasurableSpace (InfiniteAdeleRing ℚ)] [BorelSpace (InfiniteAdeleRing ℚ)]
    [mT : MeasurableSpace (InfiniteAdeleRing ℚ)ˣ] [BorelSpace (InfiniteAdeleRing ℚ)ˣ]
    (ν_add : MeasureTheory.Measure (InfiniteAdeleRing ℚ))
    (hν_add : ν_add = ENNReal.ofReal (|(a : ℝ)| ^ ((1 : ℝ) / 2)) •
      MeasureTheory.Measure.map (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).symm MeasureTheory.volume)
    (ν_mul : MeasureTheory.Measure (InfiniteAdeleRing ℚ)ˣ) [ν_mul.IsHaarMeasure]
    (ha : a ≠ 0)
    (w₀ : InfinitePlace K) (h₀ : w₀.IsReal)
    (P₂ : RealArchParam)
    (hP₂ : ((∃ (w₁ w₂ : InfinitePlace K) (h₁ : w₁.IsReal) (h₂ : w₂.IsReal),
          w₀ ≠ w₁ ∧ w₀ ≠ w₂ ∧ w₁ ≠ w₂ ∧ (∀ w : InfinitePlace K, w = w₀ ∨ w = w₁ ∨ w = w₂) ∧
          P₂ = RealArchParam.principal (uR w₁ h₁) (aR w₁ h₁) (uR w₂ h₂) (aR w₂ h₂)) ∨
        (∃ (wC : InfinitePlace K) (hC : wC.IsComplex), (∀ w : InfinitePlace K, w = wC ∨ w = w₀) ∧
          ((∃ hk : kC wC hC ≠ 0, P₂ = RealArchParam.discrete (uC wC hC) (kC wC hC).natAbs (Int.natAbs_pos.mpr hk)) ∨
           (kC wC hC = 0 ∧ P₂ = RealArchParam.principal (uC wC hC) 0 (uC wC hC) 1)))))
    (D : ArchDatumR P₂)
    (p : ℝ → ℝ → ℂ) (δ : ℕ)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => p (M 0 2) (M 1 2) * (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        ((((M 0 0 : ℝ) : ℂ) + Complex.I * ((M 1 0 : ℝ) : ℂ)) ^ 2 + (((M 0 1 : ℝ) : ℂ) + Complex.I * ((M 1 1 : ℝ) : ℂ)) ^ 2) *
        gaussian3 M)
    (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S
        (g * archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) κ)))
      = ((archWeightCharℝ (0 : ℤ) ⟨κ, hκ⟩ : ℂ))⁻¹ * jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S g := by sorry
