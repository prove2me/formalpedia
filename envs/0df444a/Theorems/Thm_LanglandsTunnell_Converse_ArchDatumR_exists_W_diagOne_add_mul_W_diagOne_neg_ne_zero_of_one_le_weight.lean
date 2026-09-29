-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_exists_W_diagOne_add_mul_W_diagOne_neg_ne_zero_of_one_le_weight
-- name    : LanglandsTunnell.Converse.ArchDatumR.exists_W_diagOne_add_mul_W_diagOne_neg_ne_zero_of_one_le_weight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/1a7e0930-465c-55a9-88ea-f5b413fea38e
-- title:
--   Weight ≥ 1 real Whittaker profiles: both parity sheets non-vanishing
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and let $\mu$ be a character of the idele class group of $K$ with values in $\mathbb{C}^\times$ which is trivial on $K^\times$, continuous and unitary. Let $uR,aR$ assign to each real place $w$ of $K$ a complex number and an element of $\mathbb{Z}/2$, and $uC,kC$ assign to each complex place a complex number and an integer, such that for every infinite place the local component of $\mu$ on $(K_w)^\times$ is $x\mapsto \|x\|^{m_w u}\,(\iota_w(x)/\|x\|)^{a}$ with $(u,a)$ the corresponding pair (with $a=(aR\,w).\mathrm{val}$ at real places). Let $\omega$ be a character of the idele class group of $\mathbb{Q}$ whose component at each real place is of the same shape with exponent $\sum_w uR\,w+\sum_w 2\,uC\,w$ and integer $\sum_w (aR\,w).\mathrm{val}+\sum_w (kC\,w+1)$, let $E$ split the infinite part of the ideles of $\mathbb{Q}$ (infinite part the identity, finite part $1$), let $a\in\mathbb{Q}$, $a\ne 0$, with unit $a_\infty$ representing it and $\psi_\infty$ the additive character $x\mapsto \mathrm{psiArch}(ax)$, and let $\nu_{\mathrm{add}}$ be $|a|^{1/2}$ times the transport of Lebesgue measure to the infinite adeles and $\nu_{\mathrm{mul}}$ a Haar measure on the infinite ideles (with the attendant measurability assumptions). Let $w_0$ be a real place of $K$ and $P_2$ a `RealArchParam` satisfying $hP_2$: either $K$ has exactly the three real places $w_0,w_1,w_2$ and $P_2=\mathrm{principal}\,(uR\,w_1)\,(aR\,w_1)\,(uR\,w_2)\,(aR\,w_2)$, or $K$ has exactly the places $w_0$ and a complex place $w_C$, and either $kC\,w_C\ne 0$ and $P_2=\mathrm{discrete}\,(uC\,w_C)\,|kC\,w_C|$, or $kC\,w_C=0$ and $P_2=\mathrm{principal}\,(uC\,w_C)\,0\,(uC\,w_C)\,1$. Let $D$ be an `ArchDatumR P₂`, that is a function $W$ on $2\times2$ real matrices, smooth on the invertible locus, with $W(n(x)g)=\psi(x)W(g)$, the central law for $P_2$, and an entire zeta family satisfying the functional equation with $\epsilon$-factor and archimedean factor of $P_2$ together with growth and decay bounds. Assume: $W(xr)=\mathrm{archWeightChar}_{\mathbb{R}}(k_0)(r)\,W(x)$ for $r$ in `rowIsometrySubgroup₀ ℝ` and $x\in GL_2(\mathbb{R})$; $W$ is a Casimir eigenfunction with eigenvalue $P_2.\mathrm{laplaceEigenvalue}$ on invertible matrices; $W$ is not identically zero on $GL_2(\mathbb{R})$; the normalisation $hk_0\mathrm{min}$, namely $k_0\in\{0,1\}$ with $k_0\equiv a_1+a_2 \pmod 2$ when $P_2$ is principal $(u_1,a_1,u_2,a_2)$, and $k_0=m+1$ when $P_2$ is discrete of parameter $m$; and $k_0\ge 1$. Then for $\varepsilon=\pm 1$ the function $\tau\mapsto W(\mathrm{diag}(\tau,1))+\varepsilon\,W(\mathrm{diag}(-\tau,1))$ is continuous on $(0,\infty)$, is non-zero at some $\tau>0$, and is non-zero on a set of $\tau>0$ of positive Lebesgue measure.
--
--   This is the two-sheet non-degeneracy of the torus profile of a real archimedean Whittaker datum of weight at least one: for weight $\ge 1$ neither the even nor the odd combination of the profile along the two half-lines can vanish identically, in contrast with weight zero, where one combination does vanish. It is used in the archimedean half of the Langlands–Tunnell converse argument, by the statements producing a non-zero Whittaker datum for a weight-one principal Levi parameter and for a discrete Levi parameter arising from the cubic induction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_exists_W_diagOne_add_mul_W_diagOne_neg_ne_zero_of_one_le_weight.lean

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

theorem LanglandsTunnell.Converse.ArchDatumR.exists_W_diagOne_add_mul_W_diagOne_neg_ne_zero_of_one_le_weight
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
    (D : ArchDatumR P₂) (k₀ : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDE : LanglandsTunnell.Converse.ArchCasimir.IsCasimirEigen D)
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0)
    (hk₀min : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P₂ = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₀ = 0 ∨ k₀ = 1) ∧ ((k₀ : ZMod 2) = a₁ + a₂)) ∧
      (∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P₂ = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1))
    (hk₀ : 1 ≤ k₀) (ε : ℂ) (hε : ε = 1 ∨ ε = -1) :
    ContinuousOn (fun τ : ℝ => D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ))) (Set.Ioi 0) ∧
      (∃ τ : ℝ, 0 < τ ∧ D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ)) ≠ 0) ∧
      0 < MeasureTheory.volume {τ : ℝ | 0 < τ ∧ D.W (ArchR.diagOne τ) + ε * D.W (ArchR.diagOne (-τ)) ≠ 0} := by sorry
