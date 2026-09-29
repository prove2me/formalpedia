-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_isReduced_adicCompletion_quotient_span_one_sub_of_pow_eq_one_of_nthSeries_eq_mul_X_pow_levelModuliPackageAbs_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.isReduced_adicCompletion_quotient_span_one_sub_of_pow_eq_one_of_nthSeries_eq_mul_X_pow_levelModuliPackageAbs_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/2ce953b2-4e0a-5c0e-831a-b712dd318068
-- title:
--   Reducedness of widehatB₀_𝔪/(1-ζ) at an ordinary point
-- statement:
--   Fix a prime $q$, naturals $\ell_g, M'$ with $M'\neq 0$, $\ell_g$ prime, $\ell_g\equiv 11\pmod{12}$, $q\nmid M'$ and $\ell_g\mid M'$, and a discrete valuation domain $A_0$ whose maximal ideal is $(q)$ and whose residue field is finite. Assume the three equivariance hypotheses entering `rigidDataH1Pow`: stability of `IsGamma1Point` (a point $(x_P,y_P)$ on the Weierstrass curve with $(W.\mathrm{pre}\Psi\,\ell_g)(x_P)=0$ and $(x_Q,y_Q)=(x_P,y_P)$) under variable change, stability of the prime-power kernel-generator condition `IsGamma0PowAt` under `kernelVariableChangeDeg`, and stability of divisibility of `inLineMulPoly` under variable change; further, a family of relative group laws $\mathcal G$ on the projective models which is chord–tangent and has the origin as identity, a level transport $\mathcal T$ for Drinfeld $q$-bases satisfying `IsSectionTransport`, and the two hypotheses `hVC`, `hCO` providing graded ring homomorphisms on the projective-model rings realising variable changes and coefficient maps. Let $P_0$ be a fine-moduli package, with ring $B_0$ of finite type over $A_0$, for the moduli datum of `rigidDataH1Pow` (a curve with unit discriminant together with $\Gamma_0(M')$ kernel polynomials, a linked $\Gamma_1(\ell_g)$-point and a Drinfeld $q$-basis, up to variable change), let $x$ be a raw point over $B_0$ whose class is the universal point, let $\mathfrak m\subset B_0$ be maximal with $q\in\mathfrak m$, and let $F_0$ be a formal group over $B_0/\mathfrak m$ whose power series is the fixed formal group law of $x$'s curve reduced mod $\mathfrak m$, with $q$-th iterate series $F_0.\mathrm{nthSeries}\ q$ equal to a unit times $X^q$. Then for every $\zeta$ in the $\mathfrak m$-adic completion of $B_0$ with $\zeta^q=1$, the quotient of that completion by the ideal $(1-\zeta)$ is reduced.
--
--   This is the ordinary-fibre reducedness statement for the completed local ring of the fine moduli ring of the level structure $H_1=\Gamma_0(M')\cap\Gamma_1(\ell_g)$ together with a Drinfeld $q$-basis, in the form used when passing from the moduli ring to its fibre over a $q$-th root of unity. It is obtained from the identification of the completion with a ring of the form $\mathrm{AdjoinRoot}$ over a power series ring, and is used in turn for the statement about reducedness after tensoring with the residue field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_isReduced_adicCompletion_quotient_span_one_sub_of_pow_eq_one_of_nthSeries_eq_mul_X_pow_levelModuliPackageAbs_rigidDataH1Pow.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.FullLevel.Diamond.isReduced_adicCompletion_quotient_span_one_sub_of_pow_eq_one_of_nthSeries_eq_mul_X_pow_levelModuliPackageAbs_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (ℓg M' : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11)
    [NeZero M'] (hM'q : ¬ q ∣ M') (hℓgM' : ℓg ∣ M')

    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : maximalIdeal A₀ = Ideal.span {(q : A₀)}) [Finite (ResidueField A₀)]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A₀ T] [CommRing T'] [Algebra A₀ T'] (f : T →ₐ[A₀] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A₀ P₀.B₀]
    (x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)
    (𝔪 : Ideal P₀.B₀) [𝔪.IsMaximal] (hq𝔪 : algebraMap A₀ P₀.B₀ (q : A₀) ∈ 𝔪)
    (F₀ : FormalGroup (P₀.B₀ ⧸ 𝔪))
    (hF₀W : F₀.toPowerSeries = (x.curve.map (Ideal.Quotient.mk 𝔪)).formalGroupLawFixed)
    (hF₀ : ∃ u : PowerSeries (P₀.B₀ ⧸ 𝔪), IsUnit u ∧ F₀.nthSeries q = u * PowerSeries.X ^ q)
    (ζ : AdicCompletion 𝔪 P₀.B₀) (hζ : ζ ^ q = 1) :
    IsReduced (AdicCompletion 𝔪 P₀.B₀ ⧸ Ideal.span {1 - ζ}) := by sorry
