-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_archDatumR_W_diagOne_neg_eq_of_weightZero
-- name    : LanglandsTunnell.CubicInduction.archDatumR_W_diagOne_neg_eq_of_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/748f6fb9-8c80-5af5-b97a-8793223adbc0
-- title:
--   Parity of the torus profile at weight zero
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and let $\mu$ be a character of the idele units of $K$ valued in $\mathbb{C}^\times$ which is trivial on principal ideles, continuous and unitary. Archimedean data are given: complex exponents $uR_w$ and signs $aR_w \in \mathbb{Z}/2$ at the real places, complex exponents $uC_w$ and integers $kC_w$ at the complex places, such that at each place the local archimedean component of $\mu$ is $x \mapsto \lVert x\rVert^{\mathrm{mult}(w)\,u}\,(x/\lVert x\rVert)^{a}$ with the corresponding pair. Further global data are carried along and are summarised here: a character $\omega$ of the rational ideles whose archimedean component at every real place of $\mathbb{Q}$ is described by the sums $\sum_w uR_w + \sum_w 2\,uC_w$ and $\sum_w aR_w + \sum_w (kC_w+1)$; a homomorphism $E$ from the infinite idele units to the idele units splitting the infinite part and trivial on the finite part; a nonzero rational $a$ with a chosen infinite idele $aInf$ above it; the additive character $x \mapsto \psi_{\mathrm{arch}}(ax)$ on the infinite adeles; the measure $\nu_{\mathrm{add}} = |a|^{1/2}$ times the transport of Lebesgue measure along the mixed-space identification, and a Haar measure $\nu_{\mathrm{mul}}$ on the infinite idele units. Fix a real place $w_0$ of $K$ and a real archimedean parameter $P_2$ which is either $\mathrm{principal}(uR_{w_1},aR_{w_1},uR_{w_2},aR_{w_2})$ when the places of $K$ are exactly three distinct real places $w_0,w_1,w_2$, or, when the places are exactly one complex place $w_C$ and $w_0$, either $\mathrm{discrete}(uC_{w_C},|kC_{w_C}|)$ if $kC_{w_C}\neq 0$ or $\mathrm{principal}(uC_{w_C},0,uC_{w_C},1)$ if $kC_{w_C}=0$. Let $D$ be an archimedean Whittaker datum for $P_2$, that is a function $W$ on real $2\times 2$ matrices, smooth on the invertible locus, with the unipotent law $W(n(x)g)=\psi(x)W(g)$, the central law governed by the central quasi-character of $P_2$, entire zeta completions satisfying the Tate-type integral formula, the functional equation with the epsilon factor of the twisted parameter, finite order in vertical strips and the decay bounds. Assume: $W$ transforms under right translation by $\mathrm{rowIsometrySubgroup}_0(\mathbb{R})$ by the weight character $\mathrm{archWeightChar}_{\mathbb{R}}$ of an integer $k_0$; $W$ is an eigenfunction of the matrix Casimir operator with eigenvalue the Laplace eigenvalue of $P_2$; $W$ is not identically zero; the minimality constraints that $k_0\in\{0,1\}$ with $k_0 \equiv a_1+a_2 \pmod 2$ whenever $P_2$ is principal with signs $a_1,a_2$, and $k_0=m+1$ whenever $P_2$ is discrete of weight $m$; and $k_0=0$. Finally let $P_2 = \mathrm{principal}(u_1,c_1,u_2,c_2)$ and let $\tau\neq 0$ be real. Then $W(\mathrm{diag}(-\tau,1)) = (-1)^{c_1}\,W(\mathrm{diag}(\tau,1))$.
--
--   This is the parity relation of the torus profile $\tau \mapsto W(\mathrm{diag}(\tau,1))$ of a minimal-weight archimedean Whittaker datum in the weight-zero (spherical) principal-series case: the profile is even or odd according to the sign $c_1 \in \mathbb{Z}/2$ of the parameter. It is obtained from the right translation law at the element $\mathrm{diag}(-1,1)$ of the row-isometry group, and is used in the cubic-induction construction of nonvanishing Whittaker vectors and in the evaluation of the associated archimedean zeta integrals, where sign cancellations across the two half-lines must be controlled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_archDatumR_W_diagOne_neg_eq_of_weightZero.lean

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

theorem LanglandsTunnell.CubicInduction.archDatumR_W_diagOne_neg_eq_of_weightZero
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
    (hk₀ : k₀ = 0)
    (u₁ u₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal u₁ c₁ u₂ c₂) (τ : ℝ) (hτ : τ ≠ 0) :
    D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c₁.val * D.W (ArchR.diagOne τ) := by sorry
