-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_jacquetVector3_mul_iota_eq_archWeightChar_inv_mul_of_conjBlockHarmonic_colHarmonic_gaussian3
-- name    : LanglandsTunnell.CubicInduction.jacquetVector3_mul_iota_eq_archWeightChar_inv_mul_of_conjBlockHarmonic_colHarmonic_gaussian3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/7173658d-b212-5bc2-87d8-fd982a413f93
-- title:
--   Equivariance of the Jacquet vector under ι of row isometries
-- statement:
--   Let $K$ be a number field with $\operatorname{finrank}_{\mathbb Q}K=3$ and let $\mu\colon (\mathbb A_K)^\times\to\mathbb C^\times$ be an admissible twist, i.e. an idele class character that is continuous and unitary. Archimedean data are given by $u_R(w)\in\mathbb C$, $a_R(w)\in\mathbb Z/2$ at the real places $w$ of $K$ and $u_C(w)\in\mathbb C$, $k_C(w)\in\mathbb Z$ at the complex places, with the hypotheses that the local component of $\mu$ at $w$ is $x\mapsto \|x\|^{\,\mathrm{mult}(w)u}\bigl(\iota_w(x)/\|x\|\bigr)^{a}$ for the corresponding pair $(u,a)$ (with $a=(a_R(w))^{\mathrm{val}}$ in the real case and $a=k_C(w)$ in the complex case). Further data, all carried along from the ambient Jacquet-vector setting and not entering the conclusion beyond fixing the notation, are summarised here: a character $\omega$ of the ideles of $\mathbb Q$ whose component at each real place has exponent $\sum_w u_R(w)+\sum_w 2u_C(w)$ and integer parameter $\sum_w (a_R(w))^{\mathrm{val}}+\sum_w(k_C(w)+1)$; a homomorphism $E$ from the infinite idele units of $\mathbb Q$ to the idele units with infinite part the identity and trivial finite part; a rational $a\neq 0$ together with an infinite-adelic unit $a_\infty$ lifting it; the additive character $\psi_\infty(x)=\psi_{\mathrm{arch}}\bigl(a\,x\bigr)$; a measure $\nu_{\mathrm{add}}=|a|^{1/2}\cdot$ (the push-forward of Lebesgue measure along the inverse of the mixed-space ring equivalence) and a Haar measure $\nu_{\mathrm{mul}}$ on the infinite idele units. Fix a real place $w_0$ of $K$ and a real archimedean parameter $P_2$ subject to the alternative: either $K$ has exactly the three real places $w_0,w_1,w_2$ and $P_2=\mathrm{principal}\,(u_R(w_1),a_R(w_1),u_R(w_2),a_R(w_2))$, or $K$ has exactly one complex place $w_C$ besides $w_0$ and $P_2=\mathrm{discrete}\,(u_C(w_C),|k_C(w_C)|)$ when $k_C(w_C)\neq0$, while $P_2=\mathrm{principal}\,(u_C(w_C),0,u_C(w_C),1)$ when $k_C(w_C)=0$. Let $D$ be an `ArchDatumR` for $P_2$, that is a Whittaker function $W$ on $2\times2$ real matrices with the smoothness, unipotent and central transformation laws, entire zeta integrals with the prescribed gamma factor and functional equation, finite order and the decay bounds. Let $p\colon\mathbb R\times\mathbb R\to\mathbb C$ be arbitrary, $m,\delta\in\mathbb N$, and let $S$ on $2\times3$ real matrices be $$S(M)=p(M_{02},M_{12})\,(M_{00}M_{11}-M_{01}M_{10})^{\delta}\,\bigl((M_{00}-iM_{10})-i(M_{01}-iM_{11})\bigr)^{m}\,e^{-\pi\sum_{i,b}M_{ib}^{2}}.$$ Then for every $\kappa$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb R)$ and every $g\in GL_3(\mathbb A_{\mathbb Q,\infty})$, the Jacquet vector `jacquetVector3` attached to $D$, the parameters $u_R(w_0),a_R(w_0)$, the real number $a$, the character $\psi_\infty$ and the section $S$, evaluated at $g$ multiplied by the archimedean component of the image of $\kappa$ under the real-place embedding $GL_2(\mathbb R)\to GL_2(\mathbb A_{\mathbb Q})$ at the unique infinite place of $\mathbb Q$ followed by the block embedding $h\mapsto \mathrm{diag}(h,1)$ into $GL_3$, equals $\bigl(\mathrm{archWeightChar}_{\mathbb R}(m)(\kappa)\bigr)^{-1}$ times its value at $g$.
--
--   This is the $K$-type computation for the Jacquet vector of the conjugate block-harmonic section times a column factor and the Gaussian: the vector is an eigenvector, with eigenvalue the inverse of the weight-$m$ character, for right translation by the block image of the row-isometry subgroup at the archimedean place. It feeds the two Rankin–Selberg statements producing a non-vanishing unfolded torus pair whose archimedean zeta integral equals the prescribed gamma factor, in the principal-series and in the discrete-series case.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_jacquetVector3_mul_iota_eq_archWeightChar_inv_mul_of_conjBlockHarmonic_colHarmonic_gaussian3.lean

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

theorem LanglandsTunnell.CubicInduction.jacquetVector3_mul_iota_eq_archWeightChar_inv_mul_of_conjBlockHarmonic_colHarmonic_gaussian3
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
    (p : ℝ → ℝ → ℂ) (m δ : ℕ)
    (S : Matrix (Fin 2) (Fin 3) ℝ → ℂ)
    (hS : S = fun M => p (M 0 2) (M 1 2) * (((M 0 0 * M 1 1 - M 0 1 * M 1 0 : ℝ) : ℂ)) ^ δ *
        (((((M 0 0 : ℝ) : ℂ) - Complex.I * ((M 1 0 : ℝ) : ℂ)) - Complex.I * (((M 0 1 : ℝ) : ℂ) - Complex.I * ((M 1 1 : ℝ) : ℂ))) ^ m) *
        gaussian3 M)
    (κ : GL (Fin 2) ℝ) (hκ : κ ∈ rowIsometrySubgroup₀ ℝ) (g : GL (Fin 3) (InfiniteAdeleRing ℚ)) :
    jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S
        (g * archComponent3 (𝓞 ℚ) ℚ (iota (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) κ)))
      = ((archWeightCharℝ (m : ℤ) ⟨κ, hκ⟩ : ℂ))⁻¹ * jacquetVector3 D (uR w₀ h₀) (aR w₀ h₀) (a : ℝ) psiInf S g := by sorry
