-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_reducesToOrigin_isDrinfeldBasisAdic_universal_of_factorsThrough_of_ne_two_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_reducesToOrigin_isDrinfeldBasisAdic_universal_of_factorsThrough_of_ne_two_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/645347a0-fdf4-5edb-8917-21a519a0576d
-- title:
--   Universal formal Drinfeld basis at a supersingular point
-- statement:
--   Fix a prime $q \neq 2$, a prime $\ell \geq 3$, a nonzero natural number $M'$ and a commutative ring $A_0$, together with two variable-change stability hypotheses: level-$\ell$ data (a quadruple $(x_P,y_P,x_Q,y_Q)$ satisfying the two Weierstrass equations, vanishing of $\mathrm{pre}\Psi_\ell$ at $x_P,x_Q$ and invertibility of the two independence elements) transform along $D \mapsto D.\mathrm{variableChange}\,C$, and the generator-kernel condition `IsGamma0PowAt` transforms along `kernelVariableChangeDeg`. Let $\mathcal{G}$ assign to each $A_0$-algebra $T$ and each projective Weierstrass curve with unit discriminant a relative group law on its $\mathrm{Proj}$ model, assumed chord-tangent (identified with affine addition, Galois-equivariantly) and with identity section given by an origin-chart homomorphism killing $x/y$ and $z/y$; let $\mathcal{T}$ be a level transport for $\mathcal{G}$ at $q$ satisfying `IsSectionTransport`. Let $P_0$ be a fine moduli package (a ring $B_0$, a universal point, and representability) for `rigidDataPow`, the rigidified datum whose level structure is a tuple of generator-kernel polynomials for the primes dividing $M'$, a level-$\ell$ structure and a Drinfeld $q$-pair, and let $x$ be a raw point over $B_0$ whose class is the universal point. Let $R$ be a Noetherian local $A_0$-algebra, complete for its maximal ideal, with surjection $\mathrm{res}_R : R \to k$ of kernel the maximal ideal, $k$ a field of characteristic $q$ in which $\ell$ and $M'$ are invertible, and let $\iota : B_0 \to R$ be an $A_0$-algebra map. Let $W_0$ be a complete discrete valuation ring with maximal ideal $(q)$ and residue field $k$ via $\mathrm{res}_0$, with $R$ a $W_0$-algebra in a scalar tower over $A_0$ and $\mathrm{res}_R$ extending $\mathrm{res}_0$. Assume the factorisation hypothesis: for each Artinian local $W_0$- and $A_0$-algebra $T$ in the tower, with residue map $\mathrm{res}_T$ onto $k$ of kernel the maximal ideal extending $\mathrm{res}_0$, every $A_0$-algebra map $\varphi : B_0 \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R \circ \iota$ extends uniquely to a residue-compatible $W_0$-algebra map $R \to T$ through $\iota$. Finally let $F$ be a commutative formal group over $R$ whose law is the fixed Weierstrass formal group law of the curve $E$ recorded by the Drinfeld component of $x_R := \iota_* x$, let $F_0$ be a commutative formal group over $k$ whose law is that of $E$ reduced along $\mathrm{res}_R$, and assume $F_0$ has $(0,0)$ as a Drinfeld basis for the zero ideal, i.e. its $q$-series is a unit times the corresponding Drinfeld divisor. The conclusion asserts the existence of ring homomorphisms $\chi_P, \chi_Q$ from the origin chart ring of $E$ to $R$ such that the sections $P$ and $Q$ of $x_R$ are the origin-chart sections of $\chi_P$, $\chi_Q$ with both origin parameters $-\chi(x/y)$ and $-\chi(z/y)$ in the maximal ideal; the law of $F_0$ is the image of that of $F$ under $\mathrm{res}_R$; the pair $(\mathrm{originParam}\,\chi_P, \mathrm{originParam}\,\chi_Q)$ is a Drinfeld basis for $F$ with respect to the maximal ideal of $R$; and, for every Artinian local $W_0$-algebra $T$ with residue map $\mathrm{res}_T$ onto $k$ of kernel the maximal ideal extending $\mathrm{res}_0$, every commutative formal group $G$ over $T$ whose law is the image of that of $F_0$ under $\mathrm{res}_T$, and all $y_0, y_1$ in the maximal ideal of $T$ forming a Drinfeld basis for $G$ there, there is a unique $W_0$-algebra map $\varphi : R \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R$ for which there exist a formal group $F'$ over $T$ obtained from $F$ by base change along $\varphi$ and an isomorphism $\psi$ of formal group laws $F' \to G$ whose series has coefficients reducing to those of $X$ modulo the maximal ideal, with $\psi$ carrying $\varphi(\mathrm{originParam}\,\chi_P)$ to $y_0$ and $\varphi(\mathrm{originParam}\,\chi_Q)$ to $y_1$.
--
--   This is the Serre–Tate style local moduli statement at a supersingular point of the full-level modular curve with auxiliary $\Gamma_0(M')$ datum, $M'$ arbitrary: the complete local ring $R$, together with the formal group of the universal curve and the two origin parameters of the Drinfeld $q$-basis, solves the deformation problem of lifting a fixed supersingular formal group over $k$ with a formal Drinfeld basis over Artinian local $W_0$-algebras. It is the source of the regularity and normality statements for the completed local rings of these modular curves used in the level-structure analysis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_reducesToOrigin_isDrinfeldBasisAdic_universal_of_factorsThrough_of_ne_two_gamma0Pow.lean

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup
attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_reducesToOrigin_isDrinfeldBasisAdic_universal_of_factorsThrough_of_ne_two_gamma0Pow
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
    (hF₀ : F₀.IsDrinfeldBasisAdic ⊥ q 0 0) :
    let xR := (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x
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
