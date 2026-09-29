-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_isReduced_levelModuliPackageAbs_gamma0Pow_of_maximalIdeal_eq_span
-- name    : ModularCurve.FullLevel.isReduced_levelModuliPackageAbs_gamma0Pow_of_maximalIdeal_eq_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/b4d15f8b-dfd1-5573-b204-35d16575bcda
-- title:
--   Reducedness of the full-level moduli ring over an unramified base
-- statement:
--   Let $q$ be a prime with $q\ge 5$, let $M'$ be a nonzero natural number with $q\nmid M'$, and let $\ell$ be a prime with $\ell\ge 3$, $\ell\neq q$ and $\ell\nmid M'$. Let $A_0$ be a discrete valuation domain whose maximal ideal is the principal ideal $(q)$, assume that some $\omega\in A_0$ is a primitive $\ell$-th root of unity, and that $\ell$ and $M'$ are units in $A_0$. Assume further: (i) the equivariance hypothesis `hℓ`, that for every $A_0$-algebra $T$ the predicate `IsLevelPStructure` at $\ell$ (two affine points $P,Q$ on $W$ killed by `preΨ` at $\ell$, with both independence elements `indepElt` units) is preserved when a Weierstrass variable change $C$ is applied to the curve and to the data by `LevelPData.variableChange`; (ii) the equivariance hypothesis `hM`, that `IsGamma0PowAt` at $(p,k)$ — the monic-of-degree-$\varphi(p^k)/2$ cyclic-kernel condition, or the two-torsion condition when $p^k=2$ — is preserved under $C$ together with `kernelVariableChangeDeg`; (iii) a family $\mathcal G$ of relative group laws on the projective models of Weierstrass curves with unit discriminant over $A_0$-algebras, chord-tangent in the sense that each member induces an additive, Galois-equivariant bijection on field-valued points, and with the identity section supported at the origin chart; (iv) a level transport $\mathcal T$ for $q$-Drinfeld bases, functorial in $A_0$-algebra maps and in variable changes and preserving the Drinfeld-basis condition, whose sections are transported compatibly with graded maps realising variable changes and coefficient changes (`IsSectionTransport`); (v) for each $A_0$-algebra and each variable change, respectively each $A_0$-algebra map, a graded ring homomorphism of the projective-model graded rings satisfying `IsVariableChangeHom`, respectively `IsCoefficientHom`, and pulling back the irrelevant ideal appropriately. Finally let $P_0$ be a fine moduli package for the level moduli datum obtained from the rigidified data `rigidDataPow` at $(\ell,M',q)$, that is, an $A_0$-algebra $B_0$ with a universal point representing the functor of Weierstrass curves with unit discriminant equipped with a $\Gamma_0(p^{k})$-type kernel polynomial for each prime power exactly dividing $M'$, a level-$\ell$ point pair and a $q$-Drinfeld basis, modulo variable change; assume $B_0$ is of finite type over $A_0$. Then $B_0$ is reduced.
--
--   This is the reducedness half of the standard local study of the fine moduli ring of a rigidified full-level moduli problem for elliptic curves over an unramified discrete valuation base, in the style of Katz–Mazur. It feeds the later identification of quotients of $B_0$ by fibres of the $j$-invariant as integral domains.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_isReduced_levelModuliPackageAbs_gamma0Pow_of_maximalIdeal_eq_span.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.isReduced_levelModuliPackageAbs_gamma0Pow_of_maximalIdeal_eq_span
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)})
    (hω : ∃ ω : A₀, IsPrimitiveRoot ω ℓ)

    (hℓA : IsUnit ((ℓ : ℕ) : A₀)) (hM'A : IsUnit ((M' : ℕ) : A₀))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
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
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A₀ P₀.B₀] :
    IsReduced P₀.B₀ := by sorry
