-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_adjoinRoot_powerSeries_of_nthSeries_eq_mul_X_pow_of_eq_one_of_ne_one_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_algEquiv_adjoinRoot_powerSeries_of_nthSeries_eq_mul_X_pow_of_eq_one_of_ne_one_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/fb70b804-0c96-5d5c-8059-9aefa874efe2
-- title:
--   Igusa presentation of the ordinary local ring, normal position
-- statement:
--   Fix a prime $q$, natural numbers $\ell_g, M'$ with $\ell_g$ prime, $\ell_g \equiv 11 \pmod{12}$, $M' \neq 0$ and $\ell_g \mid M'$, and a commutative ring $A_0$. Three equivariance hypotheses are imposed over all commutative $A_0$-algebras $T$: that $\Gamma_1(\ell_g)$-point data (a quadruple $(x_P,y_P,x_Q,y_Q)$ with $(x_P,y_P)$ on the curve, $(\mathrm{pre}\Psi_{\ell_g})(x_P)=0$ and $(x_Q,y_Q)=(x_P,y_P)$) transform under Weierstrass variable changes; that the $\Gamma_0(p^k)$-conditions on a cyclic-kernel polynomial are preserved by `kernelVariableChangeDeg`; and that divisibility of `inLineMulPoly` is likewise preserved. Given group laws $\mathcal{G}$ on the projective models which are chord-tangent and have the origin as identity, and a level transport $\mathcal{T}$ for Drinfeld $q$-bases satisfying `IsSectionTransport`, let $P_0$ be a fine moduli package for the moduli datum of `rigidDataH1Pow`, whose points over $T$ are variable-change classes of quadruples consisting of a Weierstrass curve with unit discriminant, a family of kernel polynomials indexed by the prime factors of $M'$, a $\Gamma_1(\ell_g)$-structure, a Drinfeld $q$-basis pair $(P,Q)$, and the link condition $h_{\ell_g} \mid \mathrm{inLineMulPoly}$. Let $x$ be a raw representative over $P_0.B_0$ of the universal point. Let $R$ be a noetherian local $A_0$-algebra, complete for its maximal ideal, with an $A_0$-algebra map $\iota : P_0.B_0 \to R$; let $k$ be a field of characteristic $q$ in which $\ell_g$ and $M'$ are invertible, and $\mathrm{res}_R : R \to k$ a surjection with kernel the maximal ideal. Let $W_0$ be a complete discrete valuation domain with maximal ideal $(q)$ and a surjection $\mathrm{res}_0 : W_0 \to k$ with kernel that maximal ideal, such that $R$ is a $W_0$-algebra in a scalar tower over $A_0$ and $\mathrm{res}_R$ restricts to $\mathrm{res}_0$. It is assumed that $R$ has the universal property `hfac`: for every artinian local $W_0$- and $A_0$-algebra $T$ in the tower, every surjection $\mathrm{res}_T : T \to k$ with kernel the maximal ideal lifting $\mathrm{res}_0$, and every $A_0$-algebra map $\varphi : P_0.B_0 \to T$ reducing to $\mathrm{res}_R \circ \iota$, there is a unique $W_0$-algebra map $\Phi : R \to T$ with $\mathrm{res}_T \circ \Phi = \mathrm{res}_R$ and $\Phi \circ \iota = \varphi$. Let $F_0$ be a formal group over $k$ whose law is the fixed formal group law of the reduction along $\mathrm{res}_R$ of the Weierstrass curve carried by the Drinfeld-pair component of $\iota_*x$, and assume $F_0$ is ordinary in the sense that its $q$-th iterate series equals $u\,X^q$ for some unit power series $u$. Finally, normal position is assumed: regarding $k$ as an $A_0$-algebra through $\mathrm{res}_0$, for every $A_0$-algebra map $\rho : P_0.B_0 \to k$ agreeing with $\mathrm{res}_R \circ \iota$, the curve of the Drinfeld-pair component of $\rho_*x$ has unit discriminant, its section $P$ is the identity section of the associated group law over the base, and its section $Q$ is not. The conclusion asserts the existence of a monic $g \in (W_0\llbracket X\rrbracket)[X]$ of degree $q-1$ whose coefficients in degrees $< q-1$ lie in the maximal ideal of $W_0\llbracket X\rrbracket$ and whose constant coefficient is $q$ times a unit, together with a $W_0$-algebra isomorphism $R \simeq \mathrm{AdjoinRoot}\,g$.
--
--   This is the normal-position case of the Igusa-type presentation of the completed local ring at an ordinary point of the fine moduli problem combining $\Gamma_0(M')$-, $\Gamma_1(\ell_g)$- and Drinfeld $q$-level structures: such a ring is a finite Eisenstein extension of the two-dimensional regular ring $W_0\llbracket X\rrbracket$. It feeds the version in which the normal-position hypothesis on the reduced Drinfeld pair is removed, and thence the regularity and local structure statements used for the moduli interpretation of the relevant Hecke algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_algEquiv_adjoinRoot_powerSeries_of_nthSeries_eq_mul_X_pow_of_eq_one_of_ne_one_rigidDataH1Pow.lean

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
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel IsLocalRing FormalGroup CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ModularCurve.LevelModuliPackageAbs.exists_algEquiv_adjoinRoot_powerSeries_of_nthSeries_eq_mul_X_pow_of_eq_one_of_ne_one_rigidDataH1Pow
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

    (F₀ : FormalGroup k)
    (hF₀W : F₀.toPowerSeries =
      ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR).formalGroupLawFixed)
    (hF₀ : ∃ u : PowerSeries k, IsUnit u ∧ F₀.nthSeries q = u * PowerSeries.X ^ q)

    (hnorm : letI : Algebra A₀ k := (res₀.comp (algebraMap A₀ W₀)).toAlgebra
      ∀ (ρ : P₀.B₀ →ₐ[A₀] k), (∀ b : P₀.B₀, ρ b = resR (ι b)) →
        ∃ hΔ : IsUnit ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ρ x).level.2.2.curve.Δ,
          ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ρ x).level.2.2.P =
              (𝒢 k _ hΔ).one (𝟙 (base (T := k))) ∧
          ((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ρ x).level.2.2.Q ≠
              (𝒢 k _ hΔ).one (𝟙 (base (T := k)))) :
    ∃ g : Polynomial (PowerSeries W₀), g.Monic ∧ g.natDegree = q - 1 ∧
      (∀ i < q - 1, g.coeff i ∈ maximalIdeal (PowerSeries W₀)) ∧
      (∃ u : PowerSeries W₀, IsUnit u ∧ g.coeff 0 = (q : PowerSeries W₀) * u) ∧
      Nonempty (R ≃ₐ[W₀] AdjoinRoot g) := by sorry
