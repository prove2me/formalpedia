-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_of_raw_lawIso_appAdic_eq_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algHom_of_raw_lawIso_appAdic_eq_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/fb4e03c6-b7d2-51c9-9237-8f08e7340ac9
-- title:
--   Raw Drinfeld points over T come from R
-- statement:
--   Fix a prime $q \neq 2$, a prime $\ell \geq 3$, a natural number $M' \neq 0$ and a base ring $A_0$, together with: transport hypotheses $h\ell$ and $hM$ asserting that level-$\ell$ data (a quadruple $(x_P,y_P,x_Q,y_Q)$ satisfying the affine Weierstrass equation, killed by $\mathrm{pre}\Psi_\ell$, with both independence elements units) and the predicates $\mathtt{IsGamma0PowAt}$ are preserved by Weierstrass variable changes (via `LevelPData.variableChange` and `kernelVariableChangeDeg`); a family $\mathcal{G}$ of relative group laws on projective Weierstrass models of unit discriminant which is chord–tangent and has the origin as identity; a level transport $\mathcal{T}$ for $\mathcal{G}$ at $q$ satisfying `IsSectionTransport`. Let $P_0$ be a representing package for the moduli datum of `rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯`, whose points over a ring are variable-change classes of raw data (a curve of unit discriminant, a family of $\Gamma_0$-generator polynomials indexed by the prime factors of $M'$, a level-$\ell$ quadruple, and a Drinfeld pair of sections), and let $x$ be a raw datum over $P_0.B_0$ whose class is the universal point. Let $R$ be a noetherian local ring, complete for its maximal ideal, an $A_0$-algebra, with $\iota : P_0.B_0 \to R$ an $A_0$-algebra map; let $k$ be a field of characteristic $q$ in which the images of $\ell$ and $M'$ are nonzero, and $\mathrm{res}_R : R \to k$ a surjection with kernel the maximal ideal. Let $W_0$ be a complete discrete valuation domain with maximal ideal $(q)$ and residue map $\mathrm{res}_0 : W_0 \to k$ a surjection with kernel the maximal ideal, with $R$ a $W_0$-algebra compatibly over $A_0$ and $\mathrm{res}_R \circ (W_0 \to R) = \mathrm{res}_0$. Assume the universal property $h_{\mathrm{fac}}$: for every artinian local $W_0$-algebra $T$ over $A_0$ with a surjection $\mathrm{res}_T$ onto $k$ with kernel the maximal ideal lifting $\mathrm{res}_0$, and every $A_0$-algebra map $\varphi : P_0.B_0 \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R \circ \iota$, there is a unique $W_0$-algebra map $\Phi : R \to T$ with $\mathrm{res}_T \circ \Phi = \mathrm{res}_R$ and $\Phi \circ \iota = \varphi$. Let $F$ be a commutative formal group over $R$ whose law is the fixed formal group law of the curve of the Drinfeld slot of $\iota$-pushforward of $x$, and $F_0$ a commutative formal group over $k$ with the law of the $\mathrm{res}_R$-reduction of that curve, satisfying the Drinfeld basis condition for the zero ideal at $q$ with parameters $0,0$; let $\chi_P,\chi_Q$ be ring maps from the origin chart ring of that curve to $R$ through which the sections $P$ and $Q$ reduce to the origin modulo the maximal ideal, and assume $F$ satisfies the Drinfeld basis condition for the maximal ideal of $R$ at $q$ with parameters $\mathrm{originParam}\,\chi_P$ and $\mathrm{originParam}\,\chi_Q$. Finally let $T$ be an artinian local $W_0$-algebra over $A_0$ with $\mathrm{res}_T$ as above, $G$ a commutative formal group over $T$ whose $\mathrm{res}_T$-reduction is $F_0$, and $y_0,y_1$ in the maximal ideal of $T$ such that $G$ satisfies the Drinfeld basis condition for the maximal ideal of $T$ at $q$ with parameters $y_0,y_1$; assume $h_{\mathrm{pt}}$: there is a raw datum $y_T$ over $T$, charts $\chi_{PT},\chi_{QT}$, a commutative formal group $G_T$ over $T$ with the law of $y_T$'s Drinfeld curve, and a law isomorphism $\psi : G_T \to G$ whose series reduces to $X$ modulo the maximal ideal, such that the sections of $y_T$ reduce to the origin through $\chi_{PT},\chi_{QT}$, the adic application of $\psi$ sends $\mathrm{originParam}\,\chi_{PT}$ to $y_0$ and $\mathrm{originParam}\,\chi_{QT}$ to $y_1$, and the $\mathrm{res}_T$-reductions of the curve, of the level-$\ell$ quadruple and, for each prime factor of $M'$, of the $\Gamma_0$-polynomial of $y_T$ coincide with the $\mathrm{res}_R$-reductions of those of $\iota$-pushforward of $x$. Then there is a $W_0$-algebra map $\varphi : R \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R$, a formal group $F'$ over $T$ which is the $\varphi$-base change of $F$, and a law isomorphism $\psi : F' \to G$ whose series reduces to $X$ modulo the maximal ideal of $T$, with adic application sending $\varphi(\mathrm{originParam}\,\chi_P)$ to $y_0$ and $\varphi(\mathrm{originParam}\,\chi_Q)$ to $y_1$.
--
--   This is the classification step for the $\Gamma_0$-prime-power level datum: a raw Weierstrass datum over an artinian local test ring $T$, rigidified by a Drinfeld basis of the formal group and agreeing with the fixed point over the residue field $k$, is realised by a $W_0$-algebra map from the complete local ring $R$ representing the deformation problem, compatibly with the formal groups and the Drinfeld parameters. It feeds the companion statement [`ModularCurve.LevelModuliPackageAbs.exists_algHom_isBaseChange_lawIso_appAdic_eq_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_algHom_isBaseChange_lawIso_appAdic_eq_gamma0Pow), which packages the same conclusion in base-change form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_of_raw_lawIso_appAdic_eq_gamma0Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.exists_algHom_of_raw_lawIso_appAdic_eq_gamma0Pow
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
    (hpt : ∃ (yT : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T)
      (χPT χQT : OriginChartRing yT.level.2.2.curve →+* T)
      (GT : FormalGroup T) (_ : GT.toPowerSeries = yT.level.2.2.curve.formalGroupLawFixed)
      (ψ : FormalGroup.LawIso GT G),
      (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
      ReducesToOrigin yT.level.2.2.P χPT (maximalIdeal T) ∧ ReducesToOrigin yT.level.2.2.Q χQT (maximalIdeal T) ∧
      ψ.toLawHom.appAdic (maximalIdeal T) (originParam χPT) = y₀ ∧
      ψ.toLawHom.appAdic (maximalIdeal T) (originParam χQT) = y₁ ∧

      yT.curve.map resT = (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR ∧
      yT.level.2.1.map resT = (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.1).map resR ∧
      (∀ pf : ↥M'.primeFactors, (yT.level.1 pf).map resT = (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.1 pf).map resR)) :
    ∃ φ : R →ₐ[W₀] T, (∀ r : R, resT (φ r) = resR r) ∧
        ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' G),
          (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
          ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χP)) = y₀ ∧
          ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χQ)) = y₁ := by sorry
