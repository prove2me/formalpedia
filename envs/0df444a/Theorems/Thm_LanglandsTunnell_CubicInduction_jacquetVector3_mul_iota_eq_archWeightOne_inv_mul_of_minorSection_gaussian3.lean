-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_mul_iota_eq_archWeightOne_inv_mul_of_minorSection_gaussian3
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_mul_iota_eq_archWeightOne_inv_mul_of_minorSection_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/033483e4-b674-5c16-a7dc-3f412061f2d2
-- title:
--   Weight-one K-type of the minor-section Jacquet vector
-- statement:
--   Let $K$ be a number field of degree $3$ over $\mathbb{Q}$, and let $\mu$ be a homomorphism from the idele units of $K$ to $\mathbb{C}^{\times}$ that is an admissible twist, i.e. trivial on principal ideles, continuous, and of absolute value $1$. Archimedean exponents are prescribed: data $u_R(w), a_R(w) \in \mathbb{C} \times \mathbb{Z}/2$ at the real places and $u_C(w), k_C(w) \in \mathbb{C} \times \mathbb{Z}$ at the complex places, with hypotheses `huR`, `huC` saying that on $(K_w)^{\times}$ the local component of $\mu$ is $\|x\|^{(\mathrm{mult}\,w)\,u}\,(x/\|x\|)^{a}$ with the indicated exponents; a character $\omega$ of the ideles of $\mathbb{Q}$ whose real local component has exponents the corresponding sums $\sum_{w\ \mathrm{real}} u_R(w) + \sum_{w\ \mathrm{complex}} 2u_C(w)$ and $\sum_{w\ \mathrm{real}} a_R(w) + \sum_{w\ \mathrm{complex}} (k_C(w)+1)$; a splitting $E$ of the infinite ideles into ideles with trivial finite part; a nonzero rational $a$ together with a unit $a_{\infty}$ of the infinite adele ring of $\mathbb{Q}$ whose underlying element is the image of $a$; the additive character $\psi_{\infty}(x) = \mathrm{psiArch}(a x)$; the measure $\nu_{\mathrm{add}} = |a|^{1/2}$ times the pushforward of Lebesgue measure under the inverse of the identification of the infinite adele ring with the mixed space, and a Haar measure $\nu_{\mathrm{mul}}$ on its units. Fix a real place $w_0$ of $K$ and a parameter $P_2$ of type `RealArchParam` which, by `hP₂`, is either the principal parameter built from $(u_R, a_R)$ at the two remaining real places in the case that $K$ has three real places, or, in the case that $K$ has one real place $w_0$ and one complex place $w_C$, the discrete parameter $(u_C(w_C), |k_C(w_C)|)$ when $k_C(w_C) \neq 0$ and the principal parameter $(u_C(w_C), 0, u_C(w_C), 1)$ when $k_C(w_C) = 0$. Let $D$ be an archimedean Whittaker datum `ArchDatumR` for $P_2$, and let $S$ be the minor-section Gaussian $S(M) = \bigl((M_{00} - iM_{01})M_{12} - (M_{10} - iM_{11})M_{02}\bigr)\,\exp\bigl(-\pi \sum_{i,b} M_{ib}^2\bigr)$ on real $2 \times 3$ matrices. Then for every $\kappa \in \mathrm{GL}_2(\mathbb{R})$ lying in the subgroup `rowIsometrySubgroup₀ ℝ` and every $g \in \mathrm{GL}_3$ of the infinite adele ring of $\mathbb{Q}$, the Jacquet vector `jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) a psiInf S` evaluated at $g$ multiplied on the right by the archimedean component of the image of $\kappa$ under the real-place embedding $\mathrm{GL}_2(\mathbb{R}) \to \mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ followed by the block embedding $h \mapsto \mathrm{diag}(h,1)$ into $\mathrm{GL}_3$, equals the inverse of the value of the weight character `archWeightCharℝ` of weight $1$ at $\kappa$ times the same Jacquet vector at $g$.
--
--   This records the $K$-type of the Jacquet–Whittaker vector attached to the minor-section Gaussian: it transforms under the image of the row-isometry subgroup in the first two coordinates by the inverse of the weight-one character, so the vector has weight $-1$ along that circle. It is used in the Rankin–Selberg unfolding step that produces a nonvanishing archimedean zeta value and matches the unfolded and dual torus pairings with the expected gamma factor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_mul_iota_eq_archWeightOne_inv_mul_of_minorSection_gaussian3.lean

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

theorem LanglandsTunnell.CubicInduction.jacquetVector3_mul_iota_eq_archWeightOne_inv_mul_of_minorSection_gaussian3
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
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => ((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 0 1 : ℝ) : ℂ)) * ((M 1 2 : ℝ) : ℂ) -
        (((M 1 0 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ)) * ((M 0 2 : ℝ) : ℂ)) * gaussian3 M)
    (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S
        (g * archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) κ)))
      = ((archWeightCharℝ (1 : ℤ) ⟨κ, hκ⟩ : ℂ))⁻¹ * jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S g := by sorry
