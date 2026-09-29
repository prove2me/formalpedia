-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_isBaseChange_lawIso_appAdic_eq_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algHom_isBaseChange_lawIso_appAdic_eq_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/81e110ff-568c-5575-bbc0-ac1b7cdb28b2
-- title:
--   Existence of a classifying W₀-algebra map for Drinfeld bases
-- statement:
--   Fix a prime $q\neq 2$, a prime $\ell\ge 3$, a nonzero natural number $M'$ and a commutative ring $A_0$. Assume the two transport hypotheses `hℓ` and `hM`: over every $A_0$-algebra, level-$\ell$ data satisfying `IsLevelPStructure` stay so after a variable change $C$ (applied to the data by `LevelPData.variableChange`), and polynomials satisfying `IsGamma0PowAt` for $(p,k)$ stay so after `kernelVariableChangeDeg C (gamma0PowDeg p k)`. Let $\mathcal G$ be a family of relative group laws on the projective Weierstrass models of curves with invertible discriminant over $A_0$-algebras, chord-tangent (`IsChordTangent`) and having the origin as identity (`IsOriginIdentity`), and let $\mathcal T$ be a transport of raw Drinfeld pairs satisfying `IsSectionTransport`. Let $P_0$ be a package finely representing the moduli datum attached to `rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯` — whose raw objects over $T$ are a Weierstrass curve with invertible discriminant together with a $\Gamma_0(p^{k})$-kernel tuple for the prime powers of $M'$, a level-$\ell$ datum, and a Drinfeld pair $(P,Q)$ of sections that is a Drinfeld $q$-basis for $\mathcal G$ — with representing ring $B_0$ and universal point `P₀.univ`, and let $x$ be a raw object over $B_0$ whose class modulo variable change is `P₀.univ`. Let $R$ be a Noetherian local ring, complete for the $\mathfrak m_R$-adic topology, an $A_0$-algebra, with $\iota : B_0 \to R$ an $A_0$-algebra map; let $k$ be a field of characteristic $q$ in which $\ell$ and $M'$ are nonzero, and $\mathrm{res}_R : R \to k$ a surjection with kernel $\mathfrak m_R$. Let $W_0$ be a complete discrete valuation domain with $\mathfrak m_{W_0} = (q)$ and a surjection $\mathrm{res}_0 : W_0 \to k$ with kernel $\mathfrak m_{W_0}$, with $R$ a $W_0$-algebra compatibly with $A_0$ and $\mathrm{res}_R \circ \mathrm{algebraMap} = \mathrm{res}_0$. Assume the universality hypothesis `hfac`: for every Artinian local $W_0$- and $A_0$-algebra $T$ with compatible towers and a surjection $\mathrm{res}_T : T \to k$ with kernel $\mathfrak m_T$ lifting $\mathrm{res}_0$, and every $A_0$-algebra map $\varphi : B_0 \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R \circ \iota$, there is a unique $W_0$-algebra map $\Phi : R \to T$ with $\mathrm{res}_T \circ \Phi = \mathrm{res}_R$ and $\Phi \circ \iota = \varphi$. Let $F$ be a commutative formal group over $R$ whose law is `formalGroupLawFixed` of the curve carried by the Drinfeld slot of $\iota$-pushforward of $x$, let $F_0$ be a commutative formal group over $k$ whose law is that of the $\mathrm{res}_R$-reduction of this curve and which is a Drinfeld $q$-basis at $(0,0)$ for the ideal $\bot$, let $\chi_P,\chi_Q$ be ring maps from the origin chart ring of the curve to $R$ exhibiting $P$ and $Q$ as origin-chart sections with both origin parameters in $\mathfrak m_R$, and assume $F$ is a Drinfeld $q$-basis for $\mathfrak m_R$ at $(\mathrm{originParam}\,\chi_P, \mathrm{originParam}\,\chi_Q)$, i.e. its $q$-series is a unit times the corresponding Drinfeld divisor. Then for every Artinian local $W_0$-algebra $T$ with a surjection $\mathrm{res}_T : T \to k$ of kernel $\mathfrak m_T$ lifting $\mathrm{res}_0$, every commutative formal group $G$ over $T$ whose law is the image of that of $F_0$ under $\mathrm{res}_T$, and all $y_0,y_1 \in \mathfrak m_T$ such that $G$ is a Drinfeld $q$-basis for $\mathfrak m_T$ at $(y_0,y_1)$, there exist a $W_0$-algebra map $\phi : R \to T$ with $\mathrm{res}_T \circ \phi = \mathrm{res}_R$, a formal group $F'$ over $T$ that is the $\phi$-base change of $F$, and an isomorphism $\psi$ of formal group laws $F' \to G$ (a power series with vanishing constant term, unit linear coefficient, conjugating $F'$ into $G$) whose coefficients reduce modulo $\mathfrak m_T$ to those of $X$, and such that the adic evaluations of $\psi$ at $\phi(\mathrm{originParam}\,\chi_P)$ and $\phi(\mathrm{originParam}\,\chi_Q)$ are $y_0$ and $y_1$.
--
--   This is the existence half of the classification of formal groups with Drinfeld $q$-basis over Artinian local $W_0$-algebras with residue field $k$ by $W_0$-points of the complete local ring $R$ attached to the $\Gamma_0(M')$-power level moduli problem: every such pair is, after an isomorphism of formal group laws which is the identity on the residue field, the base change of the universal datum along some $W_0$-algebra map out of $R$. It feeds the construction of the universal origin-chart and Drinfeld-basis data for the $\Gamma_0$-power datum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algHom_isBaseChange_lawIso_appAdic_eq_gamma0Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.exists_algHom_isBaseChange_lawIso_appAdic_eq_gamma0Pow
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
