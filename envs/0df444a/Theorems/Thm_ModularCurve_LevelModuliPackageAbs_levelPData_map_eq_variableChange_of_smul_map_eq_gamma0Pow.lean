-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_levelPData_map_eq_variableChange_of_smul_map_eq_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.levelPData_map_eq_variableChange_of_smul_map_eq_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/b39d8bb7-dcb2-561a-b349-4359790c1060
-- title:
--   Level-ℓ data of two lifts differ by the variable change C
-- statement:
--   Fix a prime $q \neq 2$, a prime $\ell \geq 3$, a nonzero natural number $M'$ and a commutative ring $A_0$. Assume the two transport hypotheses: `hℓ`, that for every $A_0$-algebra $T$, every Weierstrass curve $W/T$, every variable change $C$ and every `LevelPData` $D$ (a quadruple $x_P,y_P,x_Q,y_Q$), if $D$ is a level-$\ell$ structure on $W$ — both points satisfy the affine equation, $\mathrm{pre}\Psi_\ell$ vanishes at both $x$-coordinates, and both independence elements $\mathrm{indepElt}$ are units — then `D.variableChange C` is one on $C \bullet W$; and `hM`, the corresponding statement for `IsGamma0PowAt` and `kernelVariableChangeDeg` at degree `gamma0PowDeg p k`. Let $\mathcal{G}$ be a family of relative group laws that is chord–tangent and origin-identity, $\mathcal{T}$ a level transport with the section-transport property, and $P_0$ an abstract representing object, with ring $B_0$ and universal point `univ`, for the moduli datum of `rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯`; let $x$ be a raw datum over $B_0$ — a Weierstrass curve with unit discriminant together with prime-power kernel generators, a `LevelPData` $x.level.2.1$ and a Drinfeld pair, all satisfying the level conditions — whose class is `univ`. Further data, summarised here, are: a complete noetherian local $A_0$-algebra $R$ with an $A_0$-algebra map $\iota : B_0 \to R$ and residue field $k$ of characteristic $q$ in which $\ell$ and $M'$ are nonzero, via a surjection `resR` with kernel the maximal ideal; a complete discrete valuation ring $W_0$ with maximal ideal $(q)$ and residue field $k$ compatibly, with $A_0 \to W_0 \to R$ a scalar tower; the universality hypothesis `hfac`, asserting that for every artinian local $W_0$-algebra $T$ with residue field $k$ and every $A_0$-algebra map $\varphi : B_0 \to T$ reducing to `resR ∘ ι` there is a unique $W_0$-algebra map $\Phi : R \to T$ reducing to `resR` with $\Phi \circ \iota = \varphi$; commutative formal groups $F$ over $R$ and $F_0$ over $k$ equal to the fixed formal group laws of the curve of $\iota$-image of $x$ and of its reduction, with $F_0$ a Drinfeld basis for $q$ at $(0,0)$ relative to $\bot$; origin-chart homomorphisms $\chi_P, \chi_Q$ along which the two Drinfeld sections reduce to the origin, and the Drinfeld basis condition for $F$ at $(\mathrm{originParam}\,\chi_P, \mathrm{originParam}\,\chi_Q)$ relative to the maximal ideal of $R$. Now let $T$ be an artinian local $W_0$- and $A_0$-algebra in the tower, with surjection `resT` onto $k$ having kernel the maximal ideal and compatible with `res₀`, let $G$ over $T$ be the base change of $F_0$ along `resT`, and let $y_0, y_1$ lie in the maximal ideal of $T$ with $G$ a Drinfeld basis at $(y_0,y_1)$. Let $\varphi_1, \varphi_2 : R \to T$ be $W_0$-algebra maps, each reducing to `resR` and each admitting a base change $F'$ of $F$ along it together with an isomorphism of formal group laws $\psi : F' \to G$ whose series has coefficients reducing to those of $X$ and which carries the images of $\mathrm{originParam}\,\chi_P$ and $\mathrm{originParam}\,\chi_Q$ to $y_0$ and $y_1$. Finally let $C$ be a variable change over $T$ with `C.map resT = 1` and $C \bullet (x.curve$ pushed along $\varphi_1 \circ \iota) = x.curve$ pushed along $\varphi_2 \circ \iota$. The conclusion is that the level-$\ell$ point data of $x$ pushed forward along $\varphi_2 \circ \iota$ equals the $C$-transform of the level-$\ell$ point data pushed forward along $\varphi_1 \circ \iota$.
--
--   This is the level-$\ell$ component of the rigidity step for the $\Gamma_0(M')$-prime-power moduli datum: two lifts of one point of the moduli problem over an artinian local ring, related by a variable change that is trivial modulo the maximal ideal, carry level-$\ell$ data matching under that variable change. It is used in assembling the statement that two such lifts induce the same point of the moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_levelPData_map_eq_variableChange_of_smul_map_eq_gamma0Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.levelPData_map_eq_variableChange_of_smul_map_eq_gamma0Pow
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
          ψ.toLawHom.appAdic (maximalIdeal T) (φ₂ (originParam χQ)) = y₁)
    (C : WeierstrassCurve.VariableChange T) (hC : C.map resT = 1)
    (hCE : C • (x.curve.map (((φ₁.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom) = x.curve.map (((φ₂.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom) :
    x.level.2.1.map (((φ₂.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom =
      (x.level.2.1.map (((φ₁.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom).variableChange C := by sorry
