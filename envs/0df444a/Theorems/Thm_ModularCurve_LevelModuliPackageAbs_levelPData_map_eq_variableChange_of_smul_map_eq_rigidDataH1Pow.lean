-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_levelPData_map_eq_variableChange_of_smul_map_eq_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.levelPData_map_eq_variableChange_of_smul_map_eq_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/b62d4823-8138-51ce-b1b3-17af6da9ec42
-- title:
--   Equality of Γ₁(ℓ_g)-data under an infinitesimal variable change
-- statement:
--   Fix a prime $q$, naturals $\ell_g, M'$ with $\ell_g$ prime, $\ell_g \equiv 11 \pmod{12}$, $M' \neq 0$ and $\ell_g \mid M'$, and a commutative ring $A_0$. Assume the three transport hypotheses over arbitrary $A_0$-algebras $T$: $\mathtt{hℓ}$, that `IsGamma1Point` for $\ell_g$ is preserved by `LevelPData.variableChange`; $\mathtt{hM}$, that `IsGamma0PowAt` is preserved by `kernelVariableChangeDeg`; and $\mathtt{hL}$, that divisibility of `inLineMulPoly` is preserved, with $x$ replaced by $u^{-2}(x-r)$. Let $\mathcal{G}$ be a family of relative group laws on the projective models, chord–tangent and with origin the identity, and $\mathcal{T}$ a level transport for $\mathcal{G}$ and $q$ satisfying `IsSectionTransport`; these assemble the rigid datum `rigidDataH1Pow`, whose raw objects over $T$ consist of a Weierstrass curve with unit discriminant together with a tuple $(h_p)_{p \mid M'}$ of prime-power kernel generators, a `LevelPData` quadruple $(x_P,y_P,x_Q,y_Q)$ that is a $\Gamma_1(\ell_g)$-point (i.e. $(x_P,y_P)$ lies on the curve, $(W.\mathrm{pre}\Psi\,\ell_g)(x_P)=0$ and $(x_Q,y_Q)=(x_P,y_P)$), and a Drinfeld pair of sections forming a $\Gamma(q)$-basis, subject to the link condition $h_{\ell_g} \mid \mathrm{inLineMulPoly}\,W\,\ell_g\,\ell_g^{v_{\ell_g}(M')-1}\,x_P$. Let $P_0$ represent the associated moduli datum, with universal algebra $B_0 = P_0.B_0$, and let $x$ be a raw object over $B_0$ whose class is the universal point. Let $R$ be a noetherian local $A_0$-algebra, complete for its maximal ideal, $\iota : B_0 \to R$ an $A_0$-algebra map, $k$ a field of characteristic $q$ in which $\ell_g$ and $M'$ are nonzero, $\mathrm{res}_R : R \to k$ surjective with kernel $\mathfrak{m}_R$, and $W_0$ a complete discrete valuation domain with maximal ideal $(q)$ and residue field $k$ via $\mathrm{res}_0$, compatibly with $\mathrm{res}_R$ in the tower $A_0 \to W_0 \to R$. Assume the versality property $\mathtt{hfac}$: for every artinian local $W_0$-algebra $T$ in the tower with compatible surjection $\mathrm{res}_T$ onto $k$, every $A_0$-algebra map $B_0 \to T$ reducing to $\mathrm{res}_R \circ \iota$ factors through $R$ by a unique $W_0$-algebra map compatible with the residue maps. Assume further: commutative formal groups $F$ over $R$ and $F_0$ over $k$ whose power series are the fixed formal group laws of the curve of $(\mathtt{mapRing}\ \iota\ x)$ and of its reduction, $F_0$ satisfying `IsDrinfeldBasisAdic` for $\bot$, $q$, $0$, $0$; origin-chart homomorphisms $\chi_P, \chi_Q$ through which the two Drinfeld sections reduce to the origin modulo $\mathfrak{m}_R$; and $F$ satisfying `IsDrinfeldBasisAdic` for $\mathfrak{m}_R$, $q$ with parameters $\mathrm{originParam}\,\chi_P$, $\mathrm{originParam}\,\chi_Q$. Finally let $T$ be an artinian local $W_0$-algebra as above, $G$ a commutative formal group over $T$ obtained from $F_0$ by base change along $\mathrm{res}_T$, and $y_0, y_1 \in \mathfrak{m}_T$ a Drinfeld basis for $G$; let $\varphi_1, \varphi_2 : R \to T$ be $W_0$-algebra maps, each reducing to $\mathrm{res}_R$ and each admitting a base change $F'$ of $F$ along it together with an isomorphism $\psi : F' \to G$ whose coefficients reduce to those of $X$ and which carries the images of the two origin parameters to $y_0$ and $y_1$; and let $C$ be a variable change over $T$ with $C$ reducing to the identity over $k$ and with $C \cdot (x.\mathrm{curve}$ pushed along $\varphi_1 \circ \iota)$ equal to $x.\mathrm{curve}$ pushed along $\varphi_2 \circ \iota$. The conclusion is that the `LevelPData` component of $x.\mathrm{level}$ pushed along $\varphi_2 \circ \iota$ equals the `variableChange` by $C$ of the same component pushed along $\varphi_1 \circ \iota$.
--
--   This is the $\Gamma_1(\ell_g)$-slot half of the rigidity comparison for the moduli problem `rigidDataH1Pow`: once the two lifts of the universal curve to an artinian test ring are related by a variable change trivial modulo the maximal ideal, the accompanying quadruple of $\Gamma_1(\ell_g)$-point coordinates must be related by the same variable change. It is used in [`ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_rigidDataH1Pow), where the two maps $\varphi_1, \varphi_2$ are shown to carry the universal point to the same point of the moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_levelPData_map_eq_variableChange_of_smul_map_eq_rigidDataH1Pow.lean

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
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow
import Definitions.Def_WeierstrassCurve_FormalGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.levelPData_map_eq_variableChange_of_smul_map_eq_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (ℓg M' : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) [NeZero M'] (hℓgM' : ℓg ∣ M')
    (A₀ : Type) [CommRing A₀]

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
    (P₀ : LevelModuliPackageAbs A₀ (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).toLevelModuliDatum)

    (x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw P₀.B₀)
    (hx : (Quot.mk _ x : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt P₀.B₀) = P₀.univ)

    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra A₀ R] (ι : P₀.B₀ →ₐ[A₀] R)
    (k : Type) [Field k] [CharP k q] (hℓk : ((ℓg : ℕ) : k) ≠ 0) (hM'k : ((M' : ℕ) : k) ≠ 0)
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
      (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).formalGroupLawFixed)

    (F₀ : FormalGroup k) [F₀.IsComm]
    (hF₀W : F₀.toPowerSeries =
      ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR).formalGroupLawFixed)
    (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0)
    (χP χQ : OriginChartRing (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve) →+* R)
    (hP : ReducesToOrigin ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.P χP (maximalIdeal R))
    (hQ : ReducesToOrigin ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.Q χQ (maximalIdeal R))
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
