-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_reducesToOrigin_isDrinfeldBasisAdic_universal_of_factorsThrough_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_reducesToOrigin_isDrinfeldBasisAdic_universal_of_factorsThrough_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/010fd8bd-1ef1-5a39-8993-c254c8874daf
-- title:
--   Rigidified universality of the H₁ moduli ring at a supersingular point
-- statement:
--   Fix a prime $q$, a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$, and a nonzero $M'$ divisible by $\ell_g$, together with a base ring $A_0$ and the three variable-change compatibility hypotheses `hℓ`, `hM`, `hL` (stability of `IsGamma1Point`, of `IsGamma0PowAt` under `kernelVariableChangeDeg`, and of divisibility of `inLineMulPoly`) needed to form the rigid datum `rigidDataH1Pow A₀ ℓg M' q …`, whose raw points over an $A_0$-algebra are a Weierstrass curve with unit discriminant equipped with a tuple of cyclic-kernel polynomials for the prime powers of $M'$, a $\Gamma_1(\ell_g)$-point satisfying the link condition, and a Drinfeld $\Gamma(q)$-pair for the group laws $\mathcal G$ (assumed chord–tangent and origin-identity) transported by $\mathcal T$ (a section transport). Let $P_0$ be an abstract fine moduli package for this datum, with representing object $B_0$ and universal point, and let $x$ be a raw point over $B_0$ whose class is that universal point. Let $R$ be a Noetherian local $A_0$-algebra, complete for its maximal ideal, with a surjection $\mathrm{res}_R : R \to k$ onto a field $k$ of characteristic $q$ with kernel the maximal ideal, in which $\ell_g$ and $M'$ are invertible, and let $\iota : B_0 \to R$ be an $A_0$-algebra map; let $W_0$ be a complete discrete valuation ring with maximal ideal $(q)$ and residue map $\mathrm{res}_0$ onto the same $k$, with $R$ a $W_0$-algebra compatibly over $A_0$ and $\mathrm{res}_R$ extending $\mathrm{res}_0$. Assume the factorisation clause `hfac`: for every Artinian local $W_0$- and $A_0$-algebra $T$ (compatibly) with a surjection $\mathrm{res}_T$ onto $k$ with kernel the maximal ideal extending $\mathrm{res}_0$, every $A_0$-algebra map $\varphi : B_0 \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R \circ \iota$ factors uniquely through a residue-compatible $W_0$-algebra map $R \to T$. Finally let $F$ be a commutative formal group over $R$ whose power series is the fixed formal group law of the curve $E$ carried by the Drinfeld component of $x_R := \iota_* x$, let $F_0$ be a commutative formal group over $k$ whose power series is that of $E$ reduced along $\mathrm{res}_R$, and assume $(0,0)$ is a Drinfeld basis for $F_0$ relative to the zero ideal. Then there are ring homomorphisms $\chi_P, \chi_Q$ from the origin chart ring of $E$ to $R$ such that the two sections $P$, $Q$ of the Drinfeld pair are origin chart sections for them with both origin parameters in the maximal ideal, $F_0$ is the reduction of $F$ along $\mathrm{res}_R$, the pair $(\mathrm{originParam}\,\chi_P, \mathrm{originParam}\,\chi_Q)$ is a Drinfeld basis for $F$ relative to the maximal ideal of $R$, and $(R; F, \chi_P, \chi_Q)$ is universal: for every Artinian local $W_0$-algebra $T$ with a surjection $\mathrm{res}_T$ onto $k$ with kernel the maximal ideal extending $\mathrm{res}_0$, every commutative formal group $G$ over $T$ reducing to $F_0$ and every pair $y_0, y_1$ in the maximal ideal of $T$ forming a Drinfeld basis for $G$ relative to that ideal, there is a unique $W_0$-algebra map $\varphi : R \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R$ for which there exist a formal group $F'$ over $T$ that is the base change of $F$ along $\varphi$ and an isomorphism $\psi$ of formal group laws $F' \to G$ whose series has coefficients reducing to those of $X$ (the $n$-th coefficient reducing to $1$ for $n = 1$ and to $0$ otherwise) and which sends $\varphi(\mathrm{originParam}\,\chi_P)$ and $\varphi(\mathrm{originParam}\,\chi_Q)$ to $y_0$ and $y_1$ under adic substitution.
--
--   This is the Serre–Tate style statement that the completed local ring of the fine moduli scheme for the $H_1$ level datum, at a closed point whose reduced formal group is supersingular, is the universal deformation ring of that formal group rigidified by a Drinfeld $q$-basis. It is the common input to the local structure results for these moduli rings — regularity and the Hasse parameter, the integral closedness of the adic completion, and the reducedness of its quotient at a primitive root of unity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_reducesToOrigin_isDrinfeldBasisAdic_universal_of_factorsThrough_rigidDataH1Pow.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_reducesToOrigin_isDrinfeldBasisAdic_universal_of_factorsThrough_rigidDataH1Pow
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
    (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0) :
    let xR := (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x
    let E := xR.level.2.2.curve
    ∃ (χP χQ : OriginChartRing E →+* R),
      ReducesToOrigin xR.level.2.2.P χP (maximalIdeal R) ∧ ReducesToOrigin xR.level.2.2.Q χQ (maximalIdeal R) ∧
      F.IsBaseChange resR F₀ ∧
      F.IsDrinfeldBasisAdic (maximalIdeal R) q (originParam χP) (originParam χQ) ∧

      ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
        ∀ (y₀ y₁ : T), y₀ ∈ maximalIdeal T → y₁ ∈ maximalIdeal T →
        G.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁ →
          ∃! φ : R →ₐ[W₀] T, (∀ r : R, resT (φ r) = resR r) ∧
            ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' G),
              (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χP)) = y₀ ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χQ)) = y₁ := by sorry
