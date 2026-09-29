-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_raw_lawIso_appAdic_eq_of_isDrinfeldBasisAdic_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_raw_lawIso_appAdic_eq_of_isDrinfeldBasisAdic_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/665ed067-9224-5837-9679-d10ee638ceb8
-- title:
--   Lifting a Drinfeld basis to a raw Γ₀(M')-level datum
-- statement:
--   Fix a prime $q \neq 2$, a prime $\ell \geq 3$, a natural number $M' \neq 0$ and a commutative ring $A_0$, together with transport hypotheses: `hℓ` says that level-$\ell$ data (four coordinates satisfying the Weierstrass equations, killed by $\mathrm{pre}\Psi_\ell$, with the two independence elements units) are carried to such data by Weierstrass variable changes, and `hM` the same for prime-power kernel generators in the sense of `IsGamma0PowAt` under `kernelVariableChangeDeg` with the degree `gamma0PowDeg`. Fix group laws $\mathcal{G}$ on projective Weierstrass models over $A_0$-algebras that are chord-tangent and have the origin as identity section, and a level transport $\mathcal{T}$ for $\mathcal{G}$ at $q$ satisfying `IsSectionTransport`. Let `rigidDataPow` be the rigid Weierstrass datum obtained from the product of the $\Gamma_0$-component (tuples of kernel generators indexed by the prime factors of $M'$), the level-$\ell$ component and the Drinfeld component (a curve with two sections forming a Drinfeld basis for $\mathcal{G}$ at $q$). Let $P_0$ be a representing package for the associated moduli datum, with base ring $B_0$, and let $x$ be a raw datum over $B_0$ whose class is the universal point. Let $R$ be a noetherian local $A_0$-algebra, complete for its maximal ideal, $\iota : B_0 \to R$ an $A_0$-algebra map, $k$ a field of characteristic $q$ in which $\ell$ and $M'$ are invertible, $\mathrm{res}_R : R \to k$ surjective with kernel the maximal ideal; let $W_0$ be a complete discrete valuation ring with maximal ideal $(q)$ and residue field $k$ via $\mathrm{res}_0$, with $R$ a $W_0$-algebra compatibly with $A_0$ and with the residue maps. Assume the universal property `hfac`: every $A_0$-algebra map from $B_0$ to an artinian local $W_0$-algebra $T$ with residue field $k$ agreeing residually with $\iota$ extends uniquely to a $W_0$-algebra map $R \to T$ over the residue maps. Let $F$ be a commutative formal group over $R$ whose law is the fixed formal group law of the Drinfeld-component curve of $\iota_*x$, let $F_0$ be a commutative formal group over $k$ whose law is that of the reduction of this curve, with $F_0$ having Drinfeld basis $(0,0)$ at $q$ relative to the zero ideal; let $\chi_P, \chi_Q$ be origin-chart homomorphisms through which the two sections of $\iota_*x$ reduce to the origin, and assume $F$ has Drinfeld basis $(\mathrm{originParam}\,\chi_P, \mathrm{originParam}\,\chi_Q)$ at $q$ relative to the maximal ideal of $R$. Finally let $T$ be an artinian local $W_0$- and $A_0$-algebra, compatibly, with surjection $\mathrm{res}_T$ onto $k$ of kernel the maximal ideal and compatible with $\mathrm{res}_0$, let $G$ be a commutative formal group over $T$ whose reduction along $\mathrm{res}_T$ is $F_0$, and let $y_0, y_1$ lie in the maximal ideal of $T$ and form a Drinfeld basis for $G$ at $q$ relative to that ideal. The conclusion asserts the existence of a raw datum $y_T$ over $T$ (a curve with unit discriminant, a tuple of $\Gamma_0$-kernel generators over the prime factors of $M'$, a level-$\ell$ datum and a Drinfeld pair, all satisfying their levelness conditions), origin-chart homomorphisms $\chi_{P,T}, \chi_{Q,T}$ for its Drinfeld-component curve, a formal group $G_T$ over $T$ whose law is the fixed formal group law of that curve, and an isomorphism of laws $\psi : G_T \to G$ such that: every coefficient of $\psi$'s series reduces to the corresponding coefficient of $X$; the two sections of $y_T$ reduce to the origin through $\chi_{P,T}$ and $\chi_{Q,T}$; $\psi$ sends $\mathrm{originParam}\,\chi_{P,T}$ to $y_0$ and $\mathrm{originParam}\,\chi_{Q,T}$ to $y_1$ in the adic sense at the maximal ideal of $T$; and the reductions along $\mathrm{res}_T$ of the curve of $y_T$, of its level-$\ell$ datum, and of each of its kernel generators agree with the reductions along $\mathrm{res}_R$ of the corresponding data of $\iota_*x$.
--
--   This is the existence half of the comparison between formal-group data with a Drinfeld basis over an artinian base and points of the moduli problem of elliptic curves with $\Gamma_0(M')$-level, level-$\ell$ and Drinfeld $q$-basis structure, in the prime-power ($\Gamma_0$-tuple) version of the datum. It is used by [`ModularCurve.LevelModuliPackageAbs.exists_algHom_isBaseChange_lawIso_appAdic_eq_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_algHom_isBaseChange_lawIso_appAdic_eq_gamma0Pow), where the raw datum produced here is converted into an algebra homomorphism out of the representing ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_raw_lawIso_appAdic_eq_of_isDrinfeldBasisAdic_gamma0Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.exists_raw_lawIso_appAdic_eq_of_isDrinfeldBasisAdic_gamma0Pow
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
    :
    ∃ (yT : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T)
      (χPT χQT : OriginChartRing yT.level.2.2.curve →+* T)
      (GT : FormalGroup T) (_ : GT.toPowerSeries = yT.level.2.2.curve.formalGroupLawFixed)
      (ψ : FormalGroup.LawIso GT G),
      (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
      ReducesToOrigin yT.level.2.2.P χPT (maximalIdeal T) ∧ ReducesToOrigin yT.level.2.2.Q χQT (maximalIdeal T) ∧
      ψ.toLawHom.appAdic (maximalIdeal T) (originParam χPT) = y₀ ∧
      ψ.toLawHom.appAdic (maximalIdeal T) (originParam χQT) = y₁ ∧

      yT.curve.map resT = (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR ∧
      yT.level.2.1.map resT = (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.1).map resR ∧
      (∀ pf : ↥M'.primeFactors, (yT.level.1 pf).map resT = (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.1 pf).map resR) := by sorry
