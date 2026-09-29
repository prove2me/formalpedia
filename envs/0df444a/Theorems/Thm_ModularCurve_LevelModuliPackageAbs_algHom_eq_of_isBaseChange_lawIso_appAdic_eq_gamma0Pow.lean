-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_algHom_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.algHom_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/c3aa61dd-6f4a-52f3-9ac0-0cbb54a5e1ba
-- title:
--   Uniqueness of the classifying W₀-algebra map, Γ₀-power level
-- statement:
--   Fix primes $q\neq 2$ and $\ell\ge 3$, a nonzero natural number $M'$, and a commutative ring $A_0$. Two equivariance hypotheses are assumed: `hℓ`, that level-$\ell$ structures (a quadruple $(x_P,y_P,x_Q,y_Q)$ satisfying the affine equation, vanishing of $\operatorname{pre}\Psi_\ell$ at both $x$-coordinates, and invertibility of both independence elements) transport along variable changes, and `hM`, that the condition `IsGamma0PowAt` on a polynomial transports along variable changes via `kernelVariableChangeDeg` with degree `gamma0PowDeg`. Further data: a family $\mathcal G$ of relative group laws on Proj models of Weierstrass curves with invertible discriminant, chord–tangent and with identity section given by an origin chart on which $x/y$ and $z/y$ vanish; a level transport $\mathcal T$ of raw Drinfeld pairs $(\text{curve},P,Q)$ compatible with the sections; and $P_0$, an $A_0$-algebra $B_0$ with a point $\mathrm{univ}$ of the moduli functor attached to `rigidDataPow` (the rigid Weierstrass datum whose level structure is the triple: $\Gamma_0$-kernel polynomials at each prime power of $M'$, a level-$\ell$ structure, and a $q$-Drinfeld basis for $\mathcal G$) which represents it universally, together with a raw object $x$ over $B_0$ whose class is $\mathrm{univ}$. Let $R$ be a complete noetherian local $A_0$-algebra with residue map $\mathrm{res}_R$ onto a field $k$ of characteristic $q$ in which $\ell$ and $M'$ are invertible, $\iota : B_0\to R$ an $A_0$-algebra map, and $W_0$ a complete discrete valuation ring with maximal ideal $(q)$ and residue field $k$, with $R$ a $W_0$-algebra compatibly over $A_0$ and with the residue maps. Assume `hfac`: for every artinian local $W_0$- and $A_0$-algebra $T$ with surjective residue map $\mathrm{res}_T$ to $k$ whose kernel is the maximal ideal and which restricts to $\mathrm{res}_0$ on $W_0$, every $A_0$-algebra map $\varphi : B_0\to T$ lifting $\mathrm{res}_R\circ\iota$ extends uniquely to a $W_0$-algebra map $R\to T$ inducing the identity on residues. Assume also: $F$, a commutative formal group over $R$ whose law is the fixed Weierstrass formal group law of the curve of $(\mathcal T$-component of$)$ the push-forward of $x$ along $\iota$; $F_0$ over $k$, the corresponding law of the reduced curve, with $F_0$ a $q$-Drinfeld basis at $(0,0)$ for the zero ideal; origin-chart homomorphisms $\chi_P,\chi_Q$ reducing the sections $P$, $Q$ to the origin modulo the maximal ideal of $R$; and $F$ a $q$-Drinfeld basis at $(\mathrm{originParam}\,\chi_P,\mathrm{originParam}\,\chi_Q)$ for the maximal ideal of $R$. Then for every artinian local $W_0$-algebra $T$ with surjective residue map $\mathrm{res}_T$ to $k$ of kernel the maximal ideal and restricting to $\mathrm{res}_0$, every commutative formal group $G$ over $T$ obtained from $F_0$ by base change along $\mathrm{res}_T$, and all $y_0,y_1$ in the maximal ideal of $T$ with $G$ a $q$-Drinfeld basis at $(y_0,y_1)$ adically, any two $W_0$-algebra maps $\varphi_1,\varphi_2 : R\to T$ inducing $\mathrm{res}_R$ on residues and each admitting a formal group $F'$ over $T$ obtained from $F$ by base change along the map and an isomorphism $\psi$ of formal group laws $F'\to G$ whose series has $n$-th coefficient reducing to $\delta_{n,1}$ and which carries the images of $\mathrm{originParam}\,\chi_P$, $\mathrm{originParam}\,\chi_Q$ to $y_0$, $y_1$ under adic evaluation, are equal.
--
--   This is the uniqueness half of the classification of points of the rigidified Drinfeld-level moduli problem with $\Gamma_0(p^k)$-kernel data at the prime powers of $M'$: a lift $R\to T$ is pinned down by the pair (formal group up to the normalised isomorphism, Drinfeld basis) it induces. It feeds the construction of the universal object with its Drinfeld basis reducing to the origin, used in the Weierstrass-model form of the Serre–Tate/Katz–Mazur rigidification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_algHom_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.algHom_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow
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
          ∀ φ₁ φ₂ : R →ₐ[W₀] T,
            ((∀ r : R, resT (φ₁ r) = resR r) ∧
            ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ₁.toRingHom F') (ψ : FormalGroup.LawIso F' G),
              (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ₁ (originParam χP)) = y₀ ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ₁ (originParam χQ)) = y₁) →
            ((∀ r : R, resT (φ₂ r) = resR r) ∧
            ∃ (F' : FormalGroup T) (_ : F.IsBaseChange φ₂.toRingHom F') (ψ : FormalGroup.LawIso F' G),
              (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ₂ (originParam χP)) = y₀ ∧
              ψ.toLawHom.appAdic (maximalIdeal T) (φ₂ (originParam χQ)) = y₁) → φ₁ = φ₂ := by sorry
