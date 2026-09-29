-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_smooth_tensorProduct_levelModuliPackageAbs_gamma0Pow_of_isFractionRing
-- name    : ModularCurve.FullLevel.smooth_tensorProduct_levelModuliPackageAbs_gamma0Pow_of_isFractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/f37932c9-a97f-563a-b97d-bc4c1f8b21b6
-- title:
--   Smoothness of the generic fibre of the full-level moduli ring
-- statement:
--   Let $A$ be a discrete valuation domain, $q$ a prime with $5 \le q$, $M'$ a nonzero natural number with $q \nmid M'$, and $\ell$ a prime with $3 \le \ell$ and $\ell \ne q$; assume $q$ lies in the maximal ideal of $A$ and that $\ell$ and $M'$ are units in $A$. Assume the two variable-change compatibilities: over every $A$-algebra $T$, `IsLevelPStructure` at $\ell$ is preserved when a Weierstrass curve and its `LevelPData` $(x_P,y_P,x_Q,y_Q)$ are moved by a variable change $C$ via `variableChange`, and `IsGamma0PowAt` at $(p,k)$ is preserved when the kernel polynomial is moved by `kernelVariableChangeDeg` in degree `gamma0PowDeg p k`. Assume given a family $\mathcal G$ of relative group laws on the projective Weierstrass models over $A$-algebras with unit discriminant which is chord–tangent (`GroupLaws.IsChordTangent`: the points over fields carry a compatible evaluation identifying the law with affine addition) and has `GroupLaws.IsOriginIdentity`, a level transport $\mathcal T$ for pairs of sections at level $q$ satisfying `IsSectionTransport`, and the existence, for all $T$, $W$, $C$ and all $A$-algebra maps $f$, of graded ring homomorphisms of the projective model rings realising the variable change ($\mathtt{IsVariableChangeHom}$) and the coefficient map ($\mathtt{IsCoefficientHom}$), each dominating the irrelevant ideal. Let $P_0$ be a package representing the moduli datum attached by `rigidDataPow` to the product of the $\Gamma_0$-power component (for each $p \mid M'$ a monic kernel polynomial of degree $\varphi(p^{v_p(M')})/2$ satisfying `IsGamma0PowAt`), the level-$\ell$ component and the Drinfeld level-$q$ component: an $A$-algebra $B_0$ with a universal point whose image classifies every point over an $A$-algebra $T$ by a unique $A$-algebra map $B_0 \to T$. Assume $B_0$ is of finite type over $A$, and let $K$ be a field which is a fraction field of $A$, with $q \ne 0$ in $K$. Then $K \otimes_A B_0$ is a smooth $K$-algebra, i.e. formally smooth and of finite presentation.
--
--   This is the smoothness of the generic fibre of the fine moduli scheme for Weierstrass curves with a $\Gamma_0(M')$-type kernel-polynomial datum, a full level-$\ell$ structure and a Drinfeld level-$q$ structure, in the classical setting the statement that such moduli schemes are smooth over $\mathbb Z[1/(q\ell M')]$, read over the fraction field of the base. It feeds the analysis of the generic fibre: reducedness of the moduli ring, normality of its components over the fraction field, and the fact that minimal primes of the base change are not maximal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_smooth_tensorProduct_levelModuliPackageAbs_gamma0Pow_of_isFractionRing.lean

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

theorem ModularCurve.FullLevel.smooth_tensorProduct_levelModuliPackageAbs_gamma0Pow_of_isFractionRing
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q)
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)

    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
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
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    [Algebra.FiniteType A P₀.B₀]
    (K : Type) [Field K] [Algebra A K] [IsFractionRing A K]

    (hqK : (q : K) ≠ 0) :
    Algebra.Smooth K (TensorProduct A K P₀.B₀) := by sorry
