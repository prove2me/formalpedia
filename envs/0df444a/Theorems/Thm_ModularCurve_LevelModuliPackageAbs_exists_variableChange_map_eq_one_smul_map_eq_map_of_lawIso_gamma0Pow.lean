-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_variableChange_map_eq_one_smul_map_eq_map_of_lawIso_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_variableChange_map_eq_one_smul_map_eq_map_of_lawIso_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/ad77ce67-cac3-5f5d-b536-c9dfd479d732
-- title:
--   Lifts of the universal curve differ by a trivial variable change
-- statement:
--   Fix a prime $q \neq 2$, a prime $\ell \geq 3$, a natural number $M' \neq 0$ and a base ring $A_0$, together with two transport hypotheses: that level-$\ell$ data (four coordinates satisfying the two affine equations, vanishing of $\mathrm{pre}\Psi_\ell$ at both $x$-coordinates and unitness of the two independence elements) transform correctly under a Weierstrass variable change, and that the $\Gamma_0(p^k)$ kernel-generator condition `IsGamma0PowAt` is preserved by `kernelVariableChangeDeg` in degree `gamma0PowDeg`. Fix also chord–tangent group laws $\mathcal{G}$ over $A_0$ with origin as identity, a level transport $\mathcal{T}$ for $\mathcal{G}$ at $q$ satisfying `IsSectionTransport`, and a package $P_0$ representing the moduli datum of `rigidDataPow A₀ ℓ M' q`, whose points over $T$ are variable-change classes of quadruples (a Weierstrass curve with unit discriminant, a family of kernel generators indexed by the prime factors of $M'$, a level-$\ell$ datum, a Drinfeld pair of sections); let $x$ be a raw such quadruple over $B_0 = P_0.B_0$ representing the universal point. Let $R$ be a noetherian local ring, adically complete for its maximal ideal, an $A_0$-algebra, with $\iota : B_0 \to R$ an $A_0$-algebra map; let $k$ be a field of characteristic $q$ in which $\ell$ and $M'$ are nonzero, $\mathrm{res}_R : R \to k$ surjective with kernel the maximal ideal; let $W_0$ be a complete discrete valuation ring with maximal ideal $(q)$ and residue map $\mathrm{res}_0$ onto $k$, with $A_0 \to W_0 \to R$ compatible algebra structures and $\mathrm{res}_R \circ (W_0 \to R) = \mathrm{res}_0$. Assume the universality hypothesis `hfac`: for every Artinian local $W_0$-algebra $T$ with residue map to $k$ compatible with $\mathrm{res}_0$, every $A_0$-algebra map $B_0 \to T$ lifting $\mathrm{res}_R \circ \iota$ factors through a unique residue-compatible $W_0$-algebra map $R \to T$. Assume further: a commutative formal group $F$ over $R$ whose law is the fixed formal group law of the projective curve of $\iota$-pushforward of $x$; its reduction $F_0$ over $k$, the corresponding law of the reduced curve, with $F_0$ a Drinfeld basis at $q$ for the trivial ideal and parameters $0,0$; origin charts $\chi_P, \chi_Q$ for the two Drinfeld sections, each reducing to the origin modulo the maximal ideal of $R$, and $F$ a Drinfeld basis for the maximal ideal at $q$ with parameters $\mathrm{originParam}\,\chi_P$, $\mathrm{originParam}\,\chi_Q$. Finally let $T$ be an Artinian local $W_0$- and $A_0$-algebra with compatible surjection $\mathrm{res}_T$ onto $k$ of kernel the maximal ideal, $G$ a commutative formal group over $T$ obtained from $F_0$ by coefficientwise base change along $\mathrm{res}_T$, and $y_0, y_1$ in the maximal ideal making $G$ a Drinfeld basis at $q$; and let $\varphi_1, \varphi_2 : R \to T$ be $W_0$-algebra maps, each residue-compatible and each equipped with a base change $F'$ of $F$ along it and a law isomorphism $\psi : F' \to G$ whose $n$-th coefficient reduces to $\delta_{n,1}$ in $k$ and which sends the images of the two origin parameters to $y_0$ and $y_1$ respectively. Then there is a Weierstrass variable change $C$ over $T$ with $C.\mathrm{map}\ \mathrm{res}_T = 1$ and $C \bullet (x.\mathrm{curve}$ pushed forward along $\varphi_1 \circ \iota) = x.\mathrm{curve}$ pushed forward along $\varphi_2 \circ \iota$.
--
--   This is the rigidity step in the Serre–Tate/Katz–Mazur style comparison of two lifts: two $T$-valued points of the universal curve obtained from residue-compatible maps $R \to T$ with $\star$-isomorphic formal groups and matching Drinfeld parameters are related by a variable change congruent to the identity modulo the maximal ideal. It feeds [`ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow), where this variable change is used to identify the two induced moduli points; the underlying Weierstrass statement over an Artinian local ring is [`WeierstrassCurve.exists_variableChange_map_eq_one_and_smul_eq_of_lawIso_of_isArtinianRing`](thm.html#WeierstrassCurve.exists_variableChange_map_eq_one_and_smul_eq_of_lawIso_of_isArtinianRing). It is the $\Gamma_0(M')$-prime-power variant of the corresponding statement for squarefree level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_variableChange_map_eq_one_smul_map_eq_map_of_lawIso_gamma0Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.exists_variableChange_map_eq_one_smul_map_eq_map_of_lawIso_gamma0Pow
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
    :
    ∃ C : WeierstrassCurve.VariableChange T, C.map resT = 1 ∧
      C • (x.curve.map (((φ₁.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom) = x.curve.map (((φ₂.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom := by sorry
