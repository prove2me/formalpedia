-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_residue_classify_eq_of_map_residue_eq_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.residue_classify_eq_of_map_residue_eq_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/db1ded62-0677-5643-8048-febe1b692534
-- title:
--   Residue compatibility of the classifying map for `rigidDataH1Pow`
-- statement:
--   Fix a prime $q$, a prime $\ell_g$ with $\ell_g\equiv 11\pmod{12}$, a nonzero $M'$ divisible by $\ell_g$, and a commutative ring $A_0$. Let `hℓ`, `hM`, `hL` be the three transport hypotheses needed to build the datum: stability of $\Gamma_1$-points, of prime-power cyclic kernel generators (with degree shift `gamma0PowDeg`) and of divisibility by `inLineMulPoly`, under Weierstrass variable changes; let $\mathcal G$ be group laws on projective models over $A_0$-algebras which are chord-tangent and have the origin as identity, and $\mathcal T$ a level transport at $q$ which is a section transport. Write $\mathcal D$ for `rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯`, whose raw objects over an $A_0$-algebra $T$ are a Weierstrass curve with invertible discriminant together with a family of kernel generators indexed by the prime factors of $M'$ (condition `IsGamma0PowAt` at each $p^{v_p(M')}$), a point datum satisfying `IsGamma1Point` for $\ell_g$, and a Drinfeld pair (curve and two sections) forming a $\Gamma(q)$-basis for $\mathcal G$, subject to the link condition that the $\ell_g$-component divides `inLineMulPoly` at the $\Gamma_1$-point; points over $T$ are raw objects modulo variable change. Let $P_0$ be an absolute representing package for the associated moduli datum, with algebra $B_0$ and universal point `univ` represented by a raw object $x$ over $B_0$. Let $R$ be a Noetherian local $A_0$-algebra, complete for its maximal ideal, with an $A_0$-algebra map $\iota : B_0\to R$; let $k$ be a field of characteristic $q$ in which $\ell_g$ and $M'$ are nonzero, and $\mathrm{res}_R : R\to k$ surjective with kernel the maximal ideal; let $W_0$ be a complete discrete valuation domain with maximal ideal $(q)$ and surjection $\mathrm{res}_0$ onto $k$ with kernel the maximal ideal, with compatible $A_0$- and $W_0$-algebra structures on $R$ and $\mathrm{res}_R\circ\mathrm{algebraMap} = \mathrm{res}_0$. Assume `hfac`: for every Artinian local $W_0$-algebra $T$ with residue surjection $\mathrm{res}_T$ onto $k$ with kernel the maximal ideal and compatible with $\mathrm{res}_0$, and every $A_0$-algebra map $\varphi : B_0\to T$ with $\mathrm{res}_T\circ\varphi = \mathrm{res}_R\circ\iota$, there is a unique $W_0$-algebra map $\Phi : R\to T$ with $\mathrm{res}_T\circ\Phi = \mathrm{res}_R$ and $\Phi\circ\iota=\varphi$. Let $F$ be a commutative formal group over $R$ whose power series is the fixed Weierstrass formal group law of the curve of the Drinfeld pair of $\mathcal D.\mathrm{mapRing}\,\iota\,x$, and $F_0$ the corresponding one over $k$ for that curve reduced along $\mathrm{res}_R$, assumed to satisfy `IsDrinfeldBasisAdic ⊥ q 0 0`; let $\chi_P,\chi_Q$ be origin charts through which the two sections $P,Q$ of that pair factor, each with origin parameter and $w$-coordinate in the maximal ideal of $R$, and assume $F$ satisfies the Drinfeld basis condition for the maximal ideal of $R$ with parameters `originParam χP` and `originParam χQ`. Finally let $T$ be an Artinian local $W_0$-algebra with $\mathrm{res}_T$ as above, let $y_T$ be a raw object over $T$ whose two Drinfeld sections reduce to the origin via charts $\chi_{PT},\chi_{QT}$ modulo the maximal ideal of $T$, and assume that the curve of $y_T$, its $\Gamma_1$-point datum and each of its kernel polynomials have, after $\mathrm{res}_T$, the same reductions along $\mathrm{res}_R$ as those of $\mathcal D.\mathrm{mapRing}\,\iota\,x$. Then for every $b\in B_0$ one has $\mathrm{res}_T\bigl(P_0.\mathrm{classify}([y_T])(b)\bigr) = \mathrm{res}_R(\iota\, b)$, where $P_0.\mathrm{classify}([y_T])$ is the $A_0$-algebra map $B_0\to T$ carrying the universal point to the class of $y_T$.
--
--   This is the residue-compatibility step in the deformation-theoretic treatment of the moduli problem of elliptic curves with $\Gamma_0(M')$-kernel data, a $\Gamma_1(\ell_g)$-point and a Drinfeld $\Gamma(q)$-basis: a raw datum over an Artinian local base whose curve and level data have the prescribed reduction to $k$ is classified by a map that is compatible with the residue maps. It feeds the construction of the comparison algebra map in [`ModularCurve.LevelModuliPackageAbs.exists_algHom_of_raw_lawIso_appAdic_eq_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_algHom_of_raw_lawIso_appAdic_eq_rigidDataH1Pow), where the universal property `hfac` is then applied.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_residue_classify_eq_of_map_residue_eq_rigidDataH1Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.residue_classify_eq_of_map_residue_eq_rigidDataH1Pow
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
    (yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T)
    (χPT χQT : OriginChartRing yT.level.2.2.curve →+* T)
    (hPT : ReducesToOrigin yT.level.2.2.P χPT (maximalIdeal T))
    (hQT : ReducesToOrigin yT.level.2.2.Q χQT (maximalIdeal T))
    (hcurve : yT.curve.map resT = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR)
    (hlev : yT.level.2.1.map resT = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.1).map resR)
    (hker : (∀ pf : ↥M'.primeFactors, (yT.level.1 pf).map resT = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.1 pf).map resR)) :
    ∀ b : P₀.B₀,
      resT (P₀.classify (Quot.mk _ yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Pt T) b) = resR (ι b) := by sorry
