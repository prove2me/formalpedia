-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_flat_levelModuliPackageAbs_gamma0Pow_of_isDiscreteValuationRing_of_five_le
-- name    : ModularCurve.FullLevel.flat_levelModuliPackageAbs_gamma0Pow_of_isDiscreteValuationRing_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:37.725148+00:00
-- url     : https://prove2.me/theorems/9bf0fb15-e1e0-505d-914b-68df08d535b4
-- title:
--   Flatness of the full-level moduli ring over a discrete valuation ring
-- statement:
--   Let $A$ be a discrete valuation ring (a domain), let $q$ be a prime with $q \ge 5$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $\ell$ be a prime with $\ell \ge 3$ and $\ell \ne q$. Assume $q$ lies in the maximal ideal of $A$ while $\ell$ and $M'$ are units in $A$. Assume further: (i) `hℓ`, that for every $A$-algebra $T$, every Weierstrass curve $W/T$, every variable change $C$ and every quadruple $D=(x_P,y_P,x_Q,y_Q)$ in $T$, if $D$ is a level-$\ell$ structure on $W$ (both points satisfy the affine equation, $\mathrm{pre}\Psi_\ell$ vanishes at $x_P$ and at $x_Q$, and both independence elements $\mathrm{indepElt}$ are units) then the transformed quadruple `D.variableChange C` is one on $C \bullet W$; (ii) `hM`, the analogous stability of `IsGamma0PowAt W p k h` (for $p^k = 2$ the two-kernel condition on $h$, otherwise: $\deg h \le \varphi(p^k)/2$ with coefficient $1$ in that degree, $h \cdot \mathrm{pre}\Psi_{p^{k-1}} \mid \mathrm{pre}\Psi_{p^k}$, and the divisibility of the relevant multiplication numerators) under $h \mapsto$ `kernelVariableChangeDeg C (gamma0PowDeg p k) h`; (iii) a family $\mathcal G$ of relative group laws on the graded projective models of Weierstrass curves with unit discriminant over $A$-algebras, which is chord–tangent (`IsChordTangent`) and has the origin as identity (`IsOriginIdentity`); (iv) a transport $\mathcal T$ of raw Drinfeld pairs at level $q$ along $A$-algebra maps and variable changes, satisfying `IsSectionTransport`; (v) `hVC` and `hCO`, the existence of graded ring homomorphisms of the projective-model graded rings realising variable changes, respectively coefficient maps along $A$-algebra homomorphisms, each surjective enough on irrelevant ideals and satisfying `IsVariableChangeHom`, respectively `IsCoefficientHom`. Let $P_0$ be a fine-moduli package for the level moduli datum attached to `rigidDataPow A ℓ M' q`, that is, for the functor sending an $A$-algebra $T$ to the set of variable-change classes of tuples consisting of a Weierstrass curve over $T$ with unit discriminant together with a $\Gamma_0$-type prime-power kernel polynomial for each prime factor of $M'$, a level-$\ell$ structure and a Drinfeld $q$-basis; so $P_0$ consists of an $A$-algebra $B_0$ and a universal point over $B_0$ through which every $T$-point factors by a unique $A$-algebra homomorphism $B_0 \to T$. If $B_0$ is of finite type over $A$, then $B_0$ is flat as an $A$-module.
--
--   This is the flatness over the base of the Katz–Mazur fine moduli ring for the combined $\Gamma_0(M') \times \Gamma(\ell) \times \text{Drinfeld-}\Gamma(q)$ moduli problem, in the representing-object formulation used throughout this development. It feeds the local analysis of the moduli ring at residue characteristic $q$: the results on minimal primes of $B_0$, on the integrally closed quotients attached to them, and on counting those minimal primes all invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_flat_levelModuliPackageAbs_gamma0Pow_of_isDiscreteValuationRing_of_five_le.lean

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

theorem ModularCurve.FullLevel.flat_levelModuliPackageAbs_gamma0Pow_of_isDiscreteValuationRing_of_five_le
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
    [Algebra.FiniteType A P₀.B₀] :
    Module.Flat A P₀.B₀ := by sorry
