-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_levelTransport_map_eq_act_map_of_smul_map_eq_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.levelTransport_map_eq_act_map_of_smul_map_eq_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/c884c89f-bb97-57ad-917d-5c0f0a8ad3fd
-- title:
--   Drinfeld pairs transported by a variable change reducing to one
-- statement:
--   Fix a prime $q \neq 2$, a prime $\ell \ge 3$, a natural number $M' \neq 0$, a commutative base ring $A_0$, and transport hypotheses: `hℓ` says that for every $A_0$-algebra $T$, every Weierstrass curve $W$ over $T$, every variable change $C$ and every quadruple $D$ of coordinates, a level-$\ell$ structure on $W$ remains one on $C \bullet W$ after the induced change of $D$, and `hM` says that `IsGamma0PowAt W p k h` is preserved when $W$ is replaced by $C \bullet W$ and $h$ by `kernelVariableChangeDeg C (gamma0PowDeg p k) h`. Fix further a family of relative group laws $\mathcal G$ on the projective models of discriminant-unit curves, assumed chord–tangent and with origin as identity, and a level transport $\mathcal T$ for Drinfeld pairs satisfying `IsSectionTransport`. Let $P_0$ be a package representing the moduli datum of `rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯`, whose level objects are triples (prime-power kernel generators indexed by the prime factors of $M'$, level-$\ell$ data, a raw Drinfeld pair), with representing algebra $B_0$ and universal point `P₀.univ`; let $x$ be a raw object over $B_0$ whose class equals `P₀.univ`. Let $R$ be a complete noetherian local ring, $\iota : B_0 \to R$ an $A_0$-algebra map, $k$ a field of characteristic $q$ in which $\ell$ and $M'$ are invertible, `resR : R → k` surjective with kernel the maximal ideal, and $W_0$ a complete discrete valuation ring with maximal ideal $(q)$ and residue map `res₀` to $k$, compatibly with $R$; `hfac` asserts that every $A_0$-algebra map $B_0 \to T$ into an artinian local $W_0$-algebra $T$ with residue field $k$ compatible with `res₀` and agreeing with $\iota$ modulo the maximal ideal factors uniquely through a $W_0$-algebra map $R \to T$ lifting `resR`. Let $F$ be a commutative formal group over $R$ whose power series is the fixed formal group law of the curve of the Drinfeld-pair component of $\iota_*x$, $F_0$ its reduction over $k$, assumed to satisfy `IsDrinfeldBasisAdic ⊥ q 0 0`; let $\chi_P, \chi_Q$ be origin charts through which the sections $P$, $Q$ of that pair factor, each with origin parameters in the maximal ideal, and assume $F$ has Drinfeld basis $(\mathrm{originParam}\,\chi_P, \mathrm{originParam}\,\chi_Q)$ adically for the maximal ideal of $R$. Finally let $T$ be an artinian local $W_0$-algebra with surjection `resT` onto $k$ whose kernel is the maximal ideal and which is compatible with `res₀`, let $G$ be a commutative formal group over $T$ obtained from $F_0$ by base change along `resT`, with Drinfeld basis $y_0, y_1$ in the maximal ideal, and let $\varphi_1, \varphi_2 : R \to T$ be $W_0$-algebra maps, each lifting the residue map and each admitting a base change of $F$ along it together with an isomorphism onto $G$ whose series has all coefficients reducing to those of $X$ and which carries the image of the origin parameters of $\chi_P$, $\chi_Q$ to $y_0$, $y_1$. Assume $C$ is a variable change over $T$ whose reduction along `resT` is the identity and with $C \bullet (x.\mathrm{curve}$ base changed along $\varphi_1 \circ \iota) = x.\mathrm{curve}$ base changed along $\varphi_2 \circ \iota$. Then the Drinfeld pair of $x$ transported by $\mathcal T$ along $\varphi_2 \circ \iota$ equals the $\mathcal T$-action of $C$ on the one transported along $\varphi_1 \circ \iota$.
--
--   This is the uniqueness step in the comparison of two classifying maps out of the universal deformation ring: once the underlying Weierstrass curves are identified by a variable change trivial modulo the maximal ideal, the attached Drinfeld level-$q$ pairs correspond under that same variable change. It is used in [`ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow), where it yields equality of the two induced points of the moduli problem with $\Gamma_0(M')$-, level-$\ell$- and Drinfeld level-$q$-structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_levelTransport_map_eq_act_map_of_smul_map_eq_gamma0Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.levelTransport_map_eq_act_map_of_smul_map_eq_gamma0Pow
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
    𝒯.map ((φ₂.restrictScalars A₀).comp ι) x.level.2.2 = 𝒯.act C (𝒯.map ((φ₁.restrictScalars A₀).comp ι) x.level.2.2) := by sorry
