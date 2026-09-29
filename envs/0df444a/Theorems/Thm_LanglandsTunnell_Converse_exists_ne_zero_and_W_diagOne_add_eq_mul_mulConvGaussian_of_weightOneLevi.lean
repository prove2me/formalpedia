-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_ne_zero_and_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOneLevi
-- name    : LanglandsTunnell.Converse.exists_ne_zero_and_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOneLevi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/ec15e1cc-03de-5168-a40b-32e7fda88be8
-- title:
--   Non-vanishing scalar in the weight-one torus profile identity
-- statement:
--   Let $K$ be a number field with $[K:\mathbb{Q}]=3$ and let $\mu$ be a character of the idèle units of $K$ that is trivial on principal idèles, continuous and unitary. Real and complex archimedean data $u_R,a_R$ and $u_C,k_C$ are given, with $\mu$ having at each real place $w$ the local form $x\mapsto \|x\|^{\mathrm{mult}(w)u_R(w)}(x/\|x\|)^{a_R(w)}$ and at each complex place the analogous form with exponent $k_C(w)$; a character $\omega$ of the idèle units of $\mathbb{Q}$ has at its real place the exponents obtained by summing these data, as displayed. Further data: a splitting $E$ of the infinite idèle units with trivial finite part; a nonzero $a\in\mathbb{Q}$, a unit $aInf$ above it, the additive character $x\mapsto \psi_{\mathrm{arch}}(ax)$, and measures $\nu_{\mathrm{add}}$ (the $|a|^{1/2}$-scaled transport of Lebesgue measure through the mixed-space identification) and a Haar measure $\nu_{\mathrm{mul}}$. Let $w_0$ be a real place of $K$ and $P_2$ a real archimedean parameter arising, per `hP₂`, either from two further real places of $K$ (three real places in all) or from a single complex place, in the discrete or principal shape indicated. Let $D$ be an `ArchDatumR` for $P_2$, i.e. a function $W$ on $2\times2$ real matrices, smooth on the invertible locus, with the unipotent law $W(n(x)g)=\psi(x)W(g)$, the central law for $P_2$, and entire zeta integrals satisfying the functional equation, finite order and the stated decay bounds; assume $W$ transforms under right translation by the subgroup `rowIsometrySubgroup₀ ℝ` through the character `archWeightCharℝ k₀`, that $W$ is a Casimir eigenfunction with eigenvalue $P_2$'s `laplaceEigenvalue` at every invertible matrix, that $W$ is not identically zero, that $k_0$ satisfies the stated minimality constraints relative to $P_2$, and that $k_0=1$, $P_2=\mathrm{principal}(\mu_1,c_1,\mu_2,c_2)$ with $c_1\neq c_2$. Then there is $\rho\in\mathbb{C}$, $\rho\neq0$, such that for every $b\in\mathbb{Z}/2$ and every $\tau>0$, $$W(\mathrm{diag}(\tau,1))+(-1)^{b}W(\mathrm{diag}(-\tau,1))=\rho\,\tau\cdot 4\int_0^\infty r^{\mu_1+[c_1+b]}e^{-\pi r^2}\,(\tau/r)^{\mu_2+[c_2+b]}e^{-\pi(\tau/r)^2}\,\frac{dr}{r},$$ where $[\,\cdot\,]$ is `signShift`, equal to $0$ on $0$ and $1$ otherwise.
--
--   This is the weight-one principal branch of the archimedean profile computation: the two parity combinations of the torus restriction $\tau\mapsto W(\mathrm{diag}(\tau,1))$ of an archimedean Whittaker datum are identified, up to one scalar, with a multiplicative convolution of two Gaussians, and the scalar is asserted to be nonzero. It feeds the cubic-induction step that produces a nonvanishing archimedean Jacquet vector for the admissible twist.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_ne_zero_and_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOneLevi.lean

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

theorem LanglandsTunnell.Converse.exists_ne_zero_and_W_diagOne_add_eq_mul_mulConvGaussian_of_weightOneLevi
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
    (hk₀ : k₀ = 1) (μ₁ μ₂ : ℂ) (c₁ c₂ : ZMod 2) (hP₂eq : P₂ = RealArchParam.principal μ₁ c₁ μ₂ c₂) (hc : c₁ ≠ c₂) :
    ∃ ρ : ℂ, ρ ≠ 0 ∧ (∀ (b : ZMod 2) (τ : ℝ), 0 < τ →
      D.W (ArchR.diagOne τ) + (-1 : ℂ) ^ b.val * D.W (ArchR.diagOne (-τ)) = ρ * (τ : ℂ) *
        ((4 : ℂ) * ∫ r in Set.Ioi (0 : ℝ),
            ((r : ℂ) ^ (μ₁ + signShift (c₁ + b)) * (Real.exp (-(Real.pi * r ^ 2)) : ℂ)) *
              (((τ / r : ℝ) : ℂ) ^ (μ₂ + signShift (c₂ + b)) * (Real.exp (-(Real.pi * (τ / r) ^ 2)) : ℂ)) / (r : ℂ))) := by sorry
