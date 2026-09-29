-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/9a0f23d1-1b23-5d87-b73e-a71979d23f23
-- title:
--   Two rigidified lifts induce the same moduli point
-- statement:
--   Fix a prime $q \neq 2$, a prime $\ell \geq 3$, a nonzero natural number $M'$, and a commutative ring $A_0$, together with two equivariance hypotheses: `hℓ`, that for every $A_0$-algebra $T$, Weierstrass curve $W$ over $T$, variable change $C$ and quadruple $D = (x_P,y_P,x_Q,y_Q)$, if $D$ is an $\ell$-level-$P$ structure on $W$ (both points satisfy the affine equation, $(W.\mathrm{pre}\Psi\,\ell)$ vanishes at $x_P$ and at $x_Q$, and the two independence elements are units) then the transformed quadruple is such a structure on $C \bullet W$; and `hM`, the analogous statement for the predicate [`ModularCurve.IsGamma0PowAt W p k h`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) under [`ModularCurve.kernelVariableChangeDeg`](def/ModularCurve_WeierstrassLevelComponents.html#L104). Let $\mathcal{G}$ be a family of relative group laws on the projective models of discriminant-unit Weierstrass curves over $A_0$-algebras, assumed chord–tangent and with origin as identity, and $\mathcal{T}$ a level transport for $\mathcal{G}$ and $q$ satisfying `IsSectionTransport`. These data assemble the rigid Weierstrass datum `rigidDataPow`, whose raw objects over $T$ consist of a Weierstrass curve with unit discriminant equipped with prime-power kernel generators indexed by the prime factors of $M'$, an $\ell$-level-$P$ quadruple, and a Drinfeld $q$-basis pair. Let $P_0$ be an abstract level moduli package for the associated moduli datum, i.e. an $A_0$-algebra $B_0$ with a point `univ` representing the problem, and let $x$ be a raw object over $B_0$ whose class is `univ`. Let $R$ be a noetherian local $A_0$-algebra, complete for its maximal ideal, $\iota : B_0 \to R$ an $A_0$-algebra map, $k$ a field of characteristic $q$ in which $\ell$ and $M'$ are invertible, and $\mathrm{res}_R : R \to k$ surjective with kernel the maximal ideal; let $W_0$ be a complete discrete valuation ring with maximal ideal $(q)$ and residue field $k$ via $\mathrm{res}_0$, with $A_0 \to W_0 \to R$ a scalar tower compatible with the residue maps. Assume `hfac`: for every artinian local $W_0$-algebra $T$ in the tower with residue map $\mathrm{res}_T$ onto $k$ compatible with $\mathrm{res}_0$, and every $A_0$-algebra map $\varphi : B_0 \to T$ lifting $\mathrm{res}_R \circ \iota$, there is a unique $W_0$-algebra map $\Phi : R \to T$ with $\mathrm{res}_T \circ \Phi = \mathrm{res}_R$ and $\Phi \circ \iota = \varphi$. Let $F$ be a commutative formal group over $R$ whose power series is the fixed formal group law of the curve underlying $\iota_*x$, $F_0$ the corresponding object over $k$ for the reduced curve, with $F_0$ a Drinfeld $q$-basis for the zero ideal at $(0,0)$; let $\chi_P, \chi_Q$ be origin-chart homomorphisms through which the sections $P$ and $Q$ of $\iota_*x$ reduce to the origin modulo the maximal ideal of $R$, and assume $F$ is a Drinfeld $q$-basis for the maximal ideal at the origin parameters of $\chi_P, \chi_Q$. Finally let $T$ be an artinian local $W_0$-algebra in the tower with residue map $\mathrm{res}_T$ as above, $G$ a commutative formal group over $T$ obtained from $F_0$ by base change along $\mathrm{res}_T$, and $y_0, y_1$ in the maximal ideal of $T$ with $G$ a Drinfeld $q$-basis at $(y_0,y_1)$. Then for any two $W_0$-algebra maps $\varphi_1, \varphi_2 : R \to T$ each reducing to $\mathrm{res}_R$ and each admitting a formal group $F'$ over $T$ obtained from $F$ by base change along it and an isomorphism of formal group laws $\psi : F' \to G$ whose series reduces to $X$ (the residue of the $n$-th coefficient is $1$ for $n=1$ and $0$ otherwise) and which carries the images of the two origin parameters to $y_0$ and $y_1$ under its adic evaluation, the two induced $T$-points $\mathrm{map}((\varphi_i \restriction_{A_0}) \circ \iota)(P_0.\mathrm{univ})$ of the moduli datum coincide.
--
--   This is the rigidity (same-point) step in the Serre–Tate style analysis of the moduli problem combining $\Gamma_0(M')$-type prime-power kernel generators, an $\ell$-level-$P$ structure and a Drinfeld $q$-basis: two classifying homomorphisms that agree on the residue field and are compatible with the formal-group normalisation define the same point of the moduli problem over the artinian test ring. It feeds the companion statement [`ModularCurve.LevelModuliPackageAbs.algHom_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.algHom_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow), where the universal property `hfac` upgrades equality of points to equality of the two algebra maps; the proof combines the existence of a variable change matching the two raw objects with the component-wise comparisons for the kernel generators, the level-$P$ quadruple and the Drinfeld pair.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow.lean

import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_WeierstrassCurve_FormalGroupLaw
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_FormalGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
    (A₀ : Type) [CommRing A₀]

    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A₀ T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A₀) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A₀ 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)
    (k : Type) [Field k] [CharP k q] (hℓk : ((ℓ : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
    (resR : R →+* k) (hresR : Function.Surjective resR) (hkerR : RingHom.ker resR = maximalIdeal R)

    (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [IsAdicComplete (maximalIdeal W₀) W₀] (hW₀ : maximalIdeal W₀ = Ideal.span {(q : W₀)})
    (res₀ : W₀ →+* k) (hres₀ : Function.Surjective res₀) (hker₀ : RingHom.ker res₀ = maximalIdeal W₀)
    [Algebra W₀ R] [Algebra A₀ W₀] [IsScalarTower A₀ W₀ R]
    (hresR₀ : ∀ w : W₀, resR (algebraMap W₀ R w) = res₀ w)

    (hfac : ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ φ : P₀.B₀ →ₐ[A₀] T, (∀ b : P₀.B₀, resT (φ b) = resR (ι b)) →
          ∃! Φ : R →ₐ[W₀] T, (∀ r : R, resT (Φ r) = resR r) ∧ ∀ b : P₀.B₀, Φ (ι b) = φ b)

    (F : FormalGroup R) [F.IsComm]
    (hFW : F.toPowerSeries =
      (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).formalGroupLawFixed)

    (F₀ : FormalGroup k) [F₀.IsComm]
    (hF₀W : F₀.toPowerSeries =
      ((((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR).formalGroupLawFixed)
    (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (χP χQ : OriginChartRing (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve) →+* R)
    (hP : ReducesToOrigin ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.P χP (maximalIdeal R))
    (hQ : ReducesToOrigin ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.Q χQ (maximalIdeal R))
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q (originParam χP) (originParam χQ))
    (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
    [Algebra A₀ T] [IsScalarTower A₀ W₀ T]
    (resT : T →+* k) (hsT : Function.Surjective resT) (hkT : RingHom.ker resT = maximalIdeal T)
    (hT₀ : ∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w)
    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT F₀)
    (y₀ y₁ : T) (hy₀ : y₀ ∈ maximalIdeal T) (hy₁ : y₁ ∈ maximalIdeal T)
    (hDy : G.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁)
    (φ₁ φ₂ : R →ₐ[W₀] T)
    (h₁ : (∀ r : R, resT (φ₁ r) = resR r) ∧
        ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ₁.toRingHom F') (ψ : FormalGroup.LawIso F' G),
          (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
          ψ.toLawHom.appAdic (maximalIdeal T) (φ₁ (originParam χP)) = y₀ ∧
          ψ.toLawHom.appAdic (maximalIdeal T) (φ₁ (originParam χQ)) = y₁)
    (h₂ : (∀ r : R, resT (φ₂ r) = resR r) ∧
        ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ₂.toRingHom F') (ψ : FormalGroup.LawIso F' G),
          (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
          ψ.toLawHom.appAdic (maximalIdeal T) (φ₂ (originParam χP)) = y₀ ∧
          ψ.toLawHom.appAdic (maximalIdeal T) (φ₂ (originParam χQ)) = y₁) :
    (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((φ₁.restrictScalars A₀).comp ι) P₀.univ =
      (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum.map ((φ₂.restrictScalars A₀).comp ι) P₀.univ := by sorry
