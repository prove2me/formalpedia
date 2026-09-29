-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_adjoinRoot_powerSeries_of_nthSeries_eq_mul_X_pow_of_five_le_of_eq_one_of_ne_one_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algEquiv_adjoinRoot_powerSeries_of_nthSeries_eq_mul_X_pow_of_five_le_of_eq_one_of_ne_one_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/7308ab50-001c-5b27-9904-7c3979700181
-- title:
--   Igusa presentation of the completed ordinary stalk in normal position
-- statement:
--   Fix a prime $q$ with $q\neq 2$ and $5\le q$, a prime $\ell$ with $3\le\ell$, a nonzero natural number $M'$, and a commutative ring $A_0$. Assume the two equivariance clauses `hℓ` and `hM`: Katz level-$\ell$ structures (a quadruple of coordinates satisfying the Weierstrass equation, killed by `preΨ` at $\ell$, with the two independence elements units) are carried by a variable change $C$ to level-$\ell$ structures of $C\bullet W$, and the predicate `IsGamma0PowAt` at $p^k$ (a two-kernel datum when $p^k=2$, otherwise a cyclic generator polynomial of degree at most $\varphi(p^k)/2$, monic in that degree, dividing `preΨ` appropriately) is carried to `kernelVariableChangeDeg C (gamma0PowDeg p k)` of the datum. Let $\mathcal G$ be a family of relative group laws on the projective Weierstrass models of curves with unit discriminant, chord–tangent (`IsChordTangent`) and with identity at the origin chart (`IsOriginIdentity`), and $\mathcal T$ a transport of Drinfeld $\Gamma(q)$-data compatible with sections (`IsSectionTransport`). Let $P_0$ be a fine moduli package, i.e. an $A_0$-algebra $B_0$ together with a universal point `univ` representing the moduli datum attached to `rigidDataPow`, whose level data are triples consisting of a $\Gamma_0$-tuple of cyclic $p^k$-kernel polynomials for the prime powers dividing $M'$, a Katz level-$\ell$ structure, and a Drinfeld pair at $q$; and let $x$ be a raw representative over $B_0$ (a Weierstrass curve with unit discriminant together with such level data) whose class equals `P₀.univ`. Let $R$ be a complete Noetherian local $A_0$-algebra, $\iota : B_0\to R$ an $A_0$-algebra map, $k$ a field of characteristic $q$ in which $\ell$ and $M'$ are invertible, $\mathrm{res}_R : R\to k$ a surjection with kernel the maximal ideal; let $W_0$ be a complete discrete valuation ring, a domain with maximal ideal $(q)$, with a surjection $\mathrm{res}_0:W_0\to k$ with kernel the maximal ideal, together with $A_0\to W_0\to R$ forming a scalar tower and $\mathrm{res}_R\circ\mathrm{alg}_{W_0\to R}=\mathrm{res}_0$. The hypothesis `hfac` asserts the universal property of $R$: for every Artinian local $W_0$- and $A_0$-algebra $T$ in the tower, every surjection $\mathrm{res}_T:T\to k$ with kernel the maximal ideal compatible with $\mathrm{res}_0$, and every $A_0$-algebra map $\varphi:B_0\to T$ with $\mathrm{res}_T\circ\varphi=\mathrm{res}_R\circ\iota$, there is a unique $W_0$-algebra map $\Phi:R\to T$ with $\mathrm{res}_T\circ\Phi=\mathrm{res}_R$ and $\Phi\circ\iota=\varphi$. Let $F_0$ be a formal group over $k$ whose power series is the fixed formal group law of the reduction along $\mathrm{res}_R$ of the curve of the Drinfeld component of $x$ transported to $R$ by $\iota$, and assume ordinarity: `F₀.nthSeries q`, the $q$-fold iterate of the group law in one variable, equals a unit times $X^q$. Finally assume normal position (`hnorm`): for the $A_0$-algebra structure on $k$ through $W_0$, every $A_0$-algebra map $\rho:B_0\to k$ agreeing with $\mathrm{res}_R\circ\iota$ makes the discriminant of the curve of the Drinfeld component of $\rho_*x$ a unit, with its section $P$ equal to the identity section of $\mathcal G$ and its section $Q$ distinct from it. The conclusion is that there exists a monic $g\in W_0\llbracket t\rrbracket[X]$ of degree $q-1$ whose coefficients in degrees $<q-1$ lie in the maximal ideal of $W_0\llbracket t\rrbracket$, with $g$'s constant coefficient equal to $q$ times a unit, such that $R$ is isomorphic to `AdjoinRoot g` as a $W_0$-algebra.
--
--   This is the Igusa-style description of the completed local ring of the moduli problem ($\Gamma_0(M')\times\Gamma(\ell)\times$ Drinfeld $\Gamma(q)$-level) at an ordinary point whose Drinfeld basis reduces to $(O,\bar Q)$ with $\bar Q\neq O$: the stalk is $W_0\llbracket t\rrbracket[X]/(g)$ with $g$ Eisenstein of degree $q-1$ over $(q,t)$. It is the normal-position case from which the general ordinary-locus regularity statement [`ModularCurve.LevelModuliPackageAbs.exists_algEquiv_adjoinRoot_powerSeries_of_factorsThrough_of_nthSeries_eq_mul_X_pow_of_five_le_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_algEquiv_adjoinRoot_powerSeries_of_factorsThrough_of_nthSeries_eq_mul_X_pow_of_five_le_gamma0Pow) is deduced by moving the level structure by an element of $\mathrm{GL}_2(\mathbb Z/q)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_adjoinRoot_powerSeries_of_nthSeries_eq_mul_X_pow_of_five_le_of_eq_one_of_ne_one_gamma0Pow.lean

import Mathlib
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

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_algEquiv_adjoinRoot_powerSeries_of_nthSeries_eq_mul_X_pow_of_five_le_of_eq_one_of_ne_one_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hq5 : 5 ≤ q) (ℓ M' : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) [NeZero M']
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

    (F₀ : FormalGroup k)
    (hF₀W : F₀.toPowerSeries =
      ((((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR).formalGroupLawFixed)
    (hF₀ : ∃ u : PowerSeries k, IsUnit u ∧ F₀.nthSeries q = u * PowerSeries.X ^ q)

    (hnorm : letI : Algebra A₀ k := (res₀.comp (algebraMap A₀ W₀)).toAlgebra
      ∀ (ρ : P₀.B₀ →ₐ[A₀] k), (∀ b : P₀.B₀, ρ b = resR (ι b)) →
        ∃ hΔ : IsUnit ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ρ x).level.2.2.curve.Δ,
          ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ρ x).level.2.2.P =
              (𝒢 k _ hΔ).one (𝟙 (base (T := k))) ∧
          ((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ρ x).level.2.2.Q ≠
              (𝒢 k _ hΔ).one (𝟙 (base (T := k)))) :
    ∃ g : Polynomial (PowerSeries W₀), g.Monic ∧ g.natDegree = q - 1 ∧
      (∀ i < q - 1, g.coeff i ∈ maximalIdeal (PowerSeries W₀)) ∧
      (∃ u : PowerSeries W₀, IsUnit u ∧ g.coeff 0 = (q : PowerSeries W₀) * u) ∧
      Nonempty (R ≃ₐ[W₀] AdjoinRoot g) := by sorry
