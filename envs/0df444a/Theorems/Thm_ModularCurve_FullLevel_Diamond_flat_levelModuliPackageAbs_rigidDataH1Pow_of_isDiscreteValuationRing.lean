-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_flat_levelModuliPackageAbs_rigidDataH1Pow_of_isDiscreteValuationRing
-- name    : ModularCurve.FullLevel.Diamond.flat_levelModuliPackageAbs_rigidDataH1Pow_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/8be48392-94a9-5533-b1cd-4e3485c5aac5
-- title:
--   Flatness over a DVR of the H₁-level fine moduli ring
-- statement:
--   Let $A$ be a discrete valuation domain, $q$ a prime, and $M'$ a nonzero natural number with $q \nmid M'$; let $\ell_g$ be a prime with $\ell_g \equiv 11 \pmod{12}$ and $\ell_g \mid M'$. Assume the image of $q$ in $A$ lies in the maximal ideal, while $\ell_g$ and $M'$ are units in $A$. Assume further three equivariance hypotheses, valid for every $A$-algebra $T$: that [`ModularCurve.IsGamma1Point`](def/ModularCurve_WeierstrassGamma1Pow.html#L10) for $\ell_g$ (a point $(x_P,y_P)$ on the affine curve with $\mathrm{pre}\Psi_{\ell_g}(x_P)=0$ and $(x_Q,y_Q)=(x_P,y_P)$) is preserved by variable change of the underlying data; that [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) for $p^k$ (the cyclic-kernel generator conditions, or the two-torsion variant when $p^k=2$) is preserved by `kernelVariableChangeDeg`; and that divisibility of `inLineMulPoly` is preserved under the same substitution. Let $\mathcal G$ be a family of relative group laws on projective Weierstrass models with unit discriminant, satisfying chord–tangent compatibility and the origin-identity condition, and $\mathcal T$ a level transport for $\mathcal G$ at level $q$ satisfying `IsSectionTransport`. Assume also that variable changes and coefficient maps are realised by graded ring maps of the projective-model graded rings respecting irrelevant ideals (`IsVariableChangeHom`, `IsCoefficientHom`). Finally let $P_0$ be a fine moduli package for the level moduli datum of `rigidDataH1Pow A ℓg M' q …` — so $B_0 = P_0.B_0$ is an $A$-algebra carrying a universal point, universal among $A$-algebras, for the functor of elliptic curves equipped with $\Gamma_0(p^{v_p(M')})$-data for all $p \mid M'$, a $\Gamma_1(\ell_g)$-point, a Drinfeld basis of level $q$, and the linking condition that the $\ell_g$-component divides the corresponding `inLineMulPoly` at $x_P$, all modulo variable change — and assume $B_0$ is of finite type over $A$. Then $B_0$ is flat as an $A$-module.
--
--   This is the flatness over the base of the fine moduli ring of the level structure $\Gamma_0(M') \cap \Gamma_1(\ell_g)$ together with a full Drinfeld basis of level $q$, in the case of a discrete valuation base whose residue characteristic is the prime $q$ dividing the Drinfeld level. It feeds the normality and integral-closedness statements for the quotients of $B_0$ by minimal primes, used in the geometric analysis of the modular curves of full level $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_flat_levelModuliPackageAbs_rigidDataH1Pow_of_isDiscreteValuationRing.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.flat_levelModuliPackageAbs_rigidDataH1Pow_of_isDiscreteValuationRing
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)

    (hℓA : IsUnit ((ℓg : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsGamma1Point W ℓg D →
        ModularCurve.IsGamma1Point (C • W) ℓg (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (hL : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (d n : ℕ) (h : Polynomial T) (x : T), h ∣ ModularCurve.inLineMulPoly W ℓg n x →
        ModularCurve.kernelVariableChangeDeg C d h ∣
          ModularCurve.inLineMulPoly (C • W) ℓg n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)

    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataH1Pow A ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀] :
    Module.Flat A P₀.B₀ := by sorry
