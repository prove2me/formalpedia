-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_isBaseChange_lawIso_appAdic_eq_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algHom_isBaseChange_lawIso_appAdic_eq_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/0ab411f2-edb2-561a-8190-8d8bc9fc9896
-- title:
--   Existence of the classifying W₀-algebra map on formal deformations
-- statement:
--   Fix a prime $q$, natural numbers $\ell_g$ and $M'$ with $\ell_g$ prime, $\ell_g \equiv 11 \pmod{12}$, $M' \neq 0$ and $\ell_g \mid M'$, and a commutative base ring $A_0$. Assume the three equivariance hypotheses `hℓ`, `hM`, `hL` stating that the $\Gamma_1$-point condition on a `LevelPData`, the condition `IsGamma0PowAt` (a two-torsion kernel condition if $p^k = 2$, otherwise the cyclic-generator kernel conditions on a monic polynomial of degree $\varphi(p^k)/2$ dividing the division polynomials appropriately), and divisibility of `inLineMulPoly` are each preserved under Weierstrass variable changes, with the level data transported by `LevelPData.variableChange` respectively `kernelVariableChangeDeg`. Let $\mathcal{G}$ be a family of relative group laws on the projective Weierstrass models over $A_0$-algebras, chord-and-tangent and with identity section supported at the origin chart, and let $\mathcal{T}$ be a level transport for $\mathcal{G}$ and $q$ satisfying `IsSectionTransport`. Let $P_0$ be an abstract representing package for the moduli datum attached to `rigidDataH1Pow A₀ ℓg M' q …`, whose raw data consist of a Weierstrass curve with unit discriminant, a tuple of $\Gamma_0(p^{k})$-kernel polynomials for the prime powers of $M'$, a $\Gamma_1(\ell_g)$-point, and a Drinfeld basis pair for $\mathcal{G}$ at $q$, subject to the $\Gamma_1$-link divisibility; let $x$ be a raw object over $B_0 = P_0.B_0$ whose class is the universal point. Let $R$ be a Noetherian local $A_0$- and $W_0$-algebra, complete for its maximal-adic topology, with residue map $\mathrm{res}_R$ onto a field $k$ of characteristic $q$ in which $\ell_g$ and $M'$ are invertible, let $\iota : B_0 \to R$ be an $A_0$-algebra map, and let $W_0$ be a complete discrete valuation domain with maximal ideal $(q)$, residue map $\mathrm{res}_0$ onto $k$ compatible with $\mathrm{res}_R$, all in a scalar tower over $A_0$. Assume `hfac`: for every Artinian local $W_0$- and $A_0$-algebra $T$ with residue map onto $k$ compatible with $\mathrm{res}_0$, every $A_0$-algebra map $B_0 \to T$ lifting $\mathrm{res}_R \circ \iota$ factors through $R$ by a unique residue-compatible $W_0$-algebra map. Let $F$ be a commutative formal group over $R$ whose law is the fixed formal group law of the curve of $(\mathrm{mapRing}\ \iota)\,x$, let $F_0$ be a commutative formal group over $k$ whose law is that of the reduction of this curve along $\mathrm{res}_R$ and which satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`, let $\chi_P, \chi_Q$ be origin-chart ring homomorphisms to $R$ under which the two Drinfeld sections $P$ and $Q$ reduce to the origin modulo the maximal ideal, and assume $F$ has a formal Drinfeld basis at $q$ given by the origin parameters $\mathrm{originParam}\,\chi_P$, $\mathrm{originParam}\,\chi_Q$. The conclusion: for every Artinian local $W_0$-algebra $T$ with surjective $\mathrm{res}_T : T \to k$ of kernel the maximal ideal and compatible with $\mathrm{res}_0$, every commutative formal group $G$ over $T$ that is the base change of $F_0$ along $\mathrm{res}_T$, and all $y_0, y_1$ in the maximal ideal of $T$ forming a formal Drinfeld basis at $q$ for $G$, there exist a $W_0$-algebra map $\varphi : R \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R$, a formal group $F'$ over $T$ that is the base change of $F$ along $\varphi$, and an isomorphism $\psi$ of formal group laws $F' \to G$ whose series reduces to $X$ modulo the maximal ideal, such that the adic evaluation of $\psi$ sends $\varphi(\mathrm{originParam}\,\chi_P)$ to $y_0$ and $\varphi(\mathrm{originParam}\,\chi_Q)$ to $y_1$.
--
--   This is the existence half of the universality of the Serre–Tate style deformation ring $R$ for the $H_1$ level structure: every formal group lifting of $F_0$ over an Artinian local $W_0$-algebra, equipped with a formal Drinfeld basis, is induced from $(F; \mathrm{originParam}\,\chi_P, \mathrm{originParam}\,\chi_Q)$ by some classifying $W_0$-algebra map. It is used in the construction of the universal deformation with reduced-to-origin Drinfeld basis for this moduli package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_isBaseChange_lawIso_appAdic_eq_rigidDataH1Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.exists_algHom_isBaseChange_lawIso_appAdic_eq_rigidDataH1Pow
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
    (hD : F.IsDrinfeldBasisAdic (maximalIdeal R) q (originParam χP) (originParam χQ)) :
      ∀ (T : Type) [CommRing T] [IsLocalRing T] [IsArtinianRing T] [Algebra W₀ T]
        (resT : T →+* k), Function.Surjective resT → RingHom.ker resT = maximalIdeal T →
        (∀ w : W₀, resT (algebraMap W₀ T w) = res₀ w) →
        ∀ (G : FormalGroup T) [G.IsComm], G.IsBaseChange resT F₀ →
        ∀ (y₀ y₁ : T), y₀ ∈ maximalIdeal T → y₁ ∈ maximalIdeal T →
        G.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁ →
          ∃ φ : R →ₐ[W₀] T, (∀ r : R, resT (φ r) = resR r) ∧
            ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ.toRingHom F') (ψ : FormalGroup.LawIso F' G),
              (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χP)) = y₀ ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ (originParam χQ)) = y₁ := by sorry
