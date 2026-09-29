-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_isReduced_quotient_span_one_sub_of_pow_eq_one_of_factorsThrough_of_nthSeries_eq_mul_X_pow_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.isReduced_quotient_span_one_sub_of_pow_eq_one_of_factorsThrough_of_nthSeries_eq_mul_X_pow_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/281369f1-3232-5aa1-9e64-e467c46209a7
-- title:
--   Reducedness of R/(1-ζ) at an ordinary Drinfeld point
-- statement:
--   Fix primes $q$ with $q\neq 2$ and $5\le q$, and $\ell$ with $3\le\ell$, a nonzero natural number $M'$, and a commutative ring $A_0$. Assume: `hℓ`, that for every $A_0$-algebra $T$ a level-$\ell$ datum $D=(x_P,y_P,x_Q,y_Q)$ satisfying `IsLevelPStructure` (both points satisfy the affine Weierstrass equation, $\mathrm{pre}\Psi_\ell$ vanishes at $x_P$ and at $x_Q$, and both independence elements `indepElt` are units) stays such after a variable change, applied to the transformed datum `D.variableChange C`; `hM`, the analogous stability of `IsGamma0PowAt` (i.e. `IsTwoKernel` when $p^k=2$, otherwise `IsCyclicGenKernel`) under `kernelVariableChangeDeg`; a family $\mathcal G$ of relative group laws on projective Weierstrass models with unit discriminant which is chord–tangent and has the origin as identity section; a level transport $\mathcal T$ of raw Drinfeld pairs for $\mathcal G$ and $q$ which is a section transport. Let $P_0$ be a fine moduli package, with representing ring $B_0$ and universal point, for the moduli datum attached to `rigidDataPow`, the rigidified Weierstrass data obtained from the product of the $\Gamma_0(M')$-component, the level-$\ell$ component and the Drinfeld level-$q$ component; let $x$ be a raw object over $B_0$ (a Weierstrass curve with unit discriminant together with level data satisfying the level conditions) whose class is the universal point. Let $R$ be a Noetherian local $A_0$-algebra, complete for its maximal ideal, with an $A_0$-algebra map $\iota:B_0\to R$, and let $k$ be a field of characteristic $q$ in which $\ell$ and $M'$ are invertible, together with a surjection $\mathrm{res}_R:R\to k$ with kernel the maximal ideal. Let $W_0$ be a complete discrete valuation domain with maximal ideal $(q)$ and residue surjection $\mathrm{res}_0$ onto $k$, with compatible $A_0$-, $W_0$-algebra structures and $\mathrm{res}_R\circ(\text{structure map }W_0\to R)=\mathrm{res}_0$. Assume `hfac`: for every Artinian local $W_0$-algebra $T$ over $A_0$ with residue surjection onto $k$ compatible with $\mathrm{res}_0$, and every $A_0$-algebra map $\varphi:B_0\to T$ inducing $\mathrm{res}_R\circ\iota$ on residues, there is a unique $W_0$-algebra map $\Phi:R\to T$ with $\mathrm{res}_T\circ\Phi=\mathrm{res}_R$ and $\Phi\circ\iota=\varphi$. Finally let $F_0$ be a formal group over $k$ whose power series is the normalised formal group law of the reduction along $\mathrm{res}_R$ of the Weierstrass curve recorded in the Drinfeld-pair component of the level data of $x$ transported to $R$ by $\iota$, and assume its $q$-th iterated series `nthSeries q` is a unit of $k⟦X⟧$ times $X^q$. Then for any $\zeta\in R$ with $\zeta^q=1$, the quotient $R/(1-\zeta)$ is reduced.
--
--   This is the reducedness assertion of Katz–Mazur's analysis of Drinfeld level structures at an ordinary point (Arithmetic Moduli of Elliptic Curves, 13.7.6): over the deformation ring of an ordinary point of the full-level moduli problem, killing $1-\zeta$ for a $q$-th root of unity leaves a reduced ring, one Igusa branch with multiplicity one. It is used in the corresponding statement for the adic completion of the full-level fine moduli ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_isReduced_quotient_span_one_sub_of_pow_eq_one_of_factorsThrough_of_nthSeries_eq_mul_X_pow_gamma0Pow.lean

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

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.isReduced_quotient_span_one_sub_of_pow_eq_one_of_factorsThrough_of_nthSeries_eq_mul_X_pow_gamma0Pow
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

    (ζ : R) (hζ : ζ ^ q = 1) :
    IsReduced (R ⧸ Ideal.span {(1 - ζ : R)}) := by sorry
