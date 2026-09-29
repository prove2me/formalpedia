-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_levelTransport_map_eq_act_map_of_smul_map_eq_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.levelTransport_map_eq_act_map_of_smul_map_eq_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/29464320-38a4-5023-9db0-6c6dfaa0781a
-- title:
--   Transport of Drinfeld pairs under a residually trivial variable change
-- statement:
--   Fix a prime $q$, naturals $\ell_g, M'$ with $\ell_g$ prime, $\ell_g\equiv 11\pmod{12}$, $M'\neq 0$ and $\ell_g\mid M'$, and a commutative ring $A_0$. Assume the three functoriality hypotheses needed to build the level datum `rigidDataH1Pow A₀ ℓg M' q`: stability of the $\Gamma_1(\ell_g)$-point condition `IsGamma1Point` under a variable change $C$ (acting on a `LevelPData` by $(x,y)\mapsto (u^{-2}(x-r), u^{-3}(y-s(x-r)-t))$), stability of `IsGamma0PowAt` under `kernelVariableChangeDeg`, and preservation of divisibility of the in-line polynomials `inLineMulPoly`. Fix $\mathcal G$ a family of relative group laws on the projective models which is chord–tangent and has the origin as identity, and $\mathcal T$ a `LevelTransport` for $\mathcal G$ at $q$ satisfying `IsSectionTransport`; so a point of the associated moduli datum is a Weierstrass curve with unit discriminant together with a tuple of prime-power generator kernel polynomials for the primes dividing $M'$, a $\Gamma_1(\ell_g)$-point linked to that tuple, and a Drinfeld $\Gamma(q)$-basis, modulo variable change. Let $P_0$ be an abstract representing package for this datum, with universal ring $B_0$, and let $x$ be a raw object over $B_0$ whose class is the universal point. Let $R$ be a noetherian local $A_0$-algebra, complete for its maximal ideal, $\iota : B_0\to R$ an $A_0$-algebra map, $k$ a field of characteristic $q$ in which $\ell_g$ and $M'$ are nonzero, and $\mathrm{res}_R : R\to k$ surjective with kernel the maximal ideal; let $W_0$ be a complete discrete valuation ring with maximal ideal $(q)$, residue field map $\mathrm{res}_0$ onto $k$, making $R$ a $W_0$-algebra compatibly over $A_0$ and over $k$. Assume the deformation-theoretic universal property `hfac`: for every artinian local $W_0$- and $A_0$-algebra $T$ with a compatible surjection $\mathrm{res}_T$ onto $k$ with kernel the maximal ideal, and every $A_0$-algebra map $\varphi : B_0\to T$ lifting $\mathrm{res}_R\circ\iota$, there is a unique $W_0$-algebra map $\Phi : R\to T$ inducing the identity on residues and satisfying $\Phi\circ\iota=\varphi$. Let $F$ be a commutative formal group over $R$ whose power series is the fixed formal group law of the curve underlying the Drinfeld-pair component of $\iota_*x$, let $F_0$ be its analogue over $k$ for the reduction of that curve along $\mathrm{res}_R$, with $F_0$ a Drinfeld basis at $(0,0)$ for the zero ideal, let $\chi_P,\chi_Q$ be ring homomorphisms from the origin chart ring of that curve to $R$ witnessing that the two sections $P$ and $Q$ of the pair reduce to the origin modulo the maximal ideal, and assume $F$ is a Drinfeld basis at $(\mathrm{originParam}\,\chi_P, \mathrm{originParam}\,\chi_Q)$ for the maximal ideal. Now let $T$ be an artinian local $W_0$- and $A_0$-algebra with compatible surjection $\mathrm{res}_T$ onto $k$ with kernel the maximal ideal, $G$ a commutative formal group over $T$ which is the base change of $F_0$ along $\mathrm{res}_T$, and $y_0,y_1$ in the maximal ideal with $G$ a Drinfeld basis at $(y_0,y_1)$. Let $\varphi_1,\varphi_2 : R\to T$ be $W_0$-algebra maps, each inducing the identity on residues and each carrying $F$ to a formal group over $T$ equipped with an isomorphism to $G$ whose series reduces to $X$ and which sends the images of $\mathrm{originParam}\,\chi_P$ and $\mathrm{originParam}\,\chi_Q$ to $y_0$ and $y_1$. Finally let $C$ be a variable change over $T$ reducing to the identity under $\mathrm{res}_T$ such that $C$ applied to the base change of the curve of $x$ along $\varphi_1\circ\iota$ equals the base change along $\varphi_2\circ\iota$. Then the Drinfeld pair obtained by transporting the Drinfeld-pair component of the level of $x$ along $\varphi_2\circ\iota$ equals the result of acting by $C$ on the pair obtained by transporting it along $\varphi_1\circ\iota$.
--
--   This is the rigidity step for Drinfeld level structures: once two classifying maps out of the universal ring agree residually and match the Drinfeld parameters inside a formal group isomorphic to a common reduction, the variable change relating the two base-changed Weierstrass curves also transports one Drinfeld $\Gamma(q)$-basis into the other. It feeds the comparison of the two maps with the universal point, [`ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_rigidDataH1Pow), in the construction of the $\Gamma_0(M')\cap\Gamma_1(\ell_g)$-with-Drinfeld-$\Gamma(q)$ moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_levelTransport_map_eq_act_map_of_smul_map_eq_rigidDataH1Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.levelTransport_map_eq_act_map_of_smul_map_eq_rigidDataH1Pow
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
    𝒯.map ((φ₂.restrictScalars A₀).comp ι) x.level.2.2 = 𝒯.act C (𝒯.map ((φ₁.restrictScalars A₀).comp ι) x.level.2.2) := by sorry
