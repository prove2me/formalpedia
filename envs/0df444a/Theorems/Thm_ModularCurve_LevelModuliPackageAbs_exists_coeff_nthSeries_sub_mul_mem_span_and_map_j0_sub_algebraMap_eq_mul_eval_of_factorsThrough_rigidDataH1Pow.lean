-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_coeff_nthSeries_sub_mul_mem_span_and_map_j0_sub_algebraMap_eq_mul_eval_of_factorsThrough_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_coeff_nthSeries_sub_mul_mem_span_and_map_j0_sub_algebraMap_eq_mul_eval_of_factorsThrough_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/0a53711b-cfd8-5e96-8b93-7250147496b9
-- title:
--   Hasse parameter and j at a supersingular Drinfeld point
-- statement:
--   Fix a prime $q$, a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$, a nonzero natural number $M'$ divisible by $\ell_g$, and a commutative ring $A_0$. Three hypotheses `hℓ`, `hM`, `hL` assert that the level conditions entering `rigidDataH1Pow` are stable under Weierstrass variable changes, namely the $\Gamma_1$-point condition `IsGamma1Point` at $\ell_g$ (the marked point $(x_P,y_P)$ satisfies the affine equation, $\mathrm{pre}\Psi_{\ell_g}$ vanishes at $x_P$, and $(x_Q,y_Q)=(x_P,y_P)$), the $\Gamma_0$-power kernel condition `IsGamma0PowAt`, and divisibility of `inLineMulPoly` under `kernelVariableChangeDeg`; they are summarised here. Further data: group laws $\mathcal{G}$ on projective Weierstrass models over $A_0$-algebras which are chord–tangent and have the origin as identity, a level transport $\mathcal{T}$ of level $q$ satisfying `IsSectionTransport`, and a fine moduli package $P_0$ for the resulting rigid datum: an $A_0$-algebra $B_0$ with a universal point through which every point over an $A_0$-algebra factors uniquely. Let $x$ be a raw object over $B_0$ (a Weierstrass curve of unit discriminant together with a polynomial for each prime factor of $M'$ satisfying the $\Gamma_0$-power condition, a level-$P$ datum satisfying the $\Gamma_1$-condition, a Drinfeld pair of level $q$, and the $\Gamma_1$-link divisibility) whose class modulo variable changes is the universal point. Let $R$ be a complete noetherian local $A_0$-algebra with $\iota : B_0 \to R$, residue field $k$ of characteristic $q$ via a surjection $\mathrm{res}_R$ with kernel the maximal ideal, in which $\ell_g$ and $M'$ are invertible; let $W_0$ be a complete discrete valuation domain with maximal ideal $(q)$ and residue field $k$, with $R$ a $W_0$-algebra compatibly over $A_0$ and residue-compatibly. Hypothesis `hfac` states that $R$ is the universal such deformation ring: for every Artinian local $W_0$- and $A_0$-algebra $T$ with residue map onto $k$ compatible with $\mathrm{res}_0$, every $A_0$-algebra map $\varphi : B_0 \to T$ lifting $\mathrm{res}_R \circ \iota$ factors through a unique residue-compatible $W_0$-algebra map $R \to T$. Finally $F$ is a commutative formal group over $R$ whose series is the fixed Weierstrass formal group law of the curve carried by the Drinfeld component of $\iota_*x$, $F_0$ is a commutative formal group over $k$ whose series is that law for the reduction of the same curve along $\mathrm{res}_R$, and `hF₀` asserts `F₀.IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. the multiplication-by-$q$ series $F_0$.`nthSeries` $q$ is a unit power series times `F₀.drinfeldDivisor q 0 0`. The conclusion produces $T, w \in R$ with $w$ a unit and $\mathrm{coeff}_q(F.\mathrm{nthSeries}\ q) - wT \in (q)R$, an element $a_0 \in W_0$, a natural number $k \ge 1$ (this binder shadows the residue field), a unit $w' \in R$, and a monic $P \in W_0[X]$ of degree $k$ whose coefficients satisfy $P_i \in \mathfrak{m}_{W_0}^{\lfloor (k-i)q/(q+1)\rfloor + 1}$ for $i < k$, such that $\iota(j_0) - a_0 = w' \cdot P(T)$, where $j_0$ is the element `P₀.j₀` of $B_0$ attached to the universal point and $P$ is mapped into $R$ along $W_0 \to R$.
--
--   This is the local structure of the $j$-line at a supersingular point of the moduli problem with Drinfeld level-$q$ structure together with $\Gamma_0(M')$- and $\Gamma_1(\ell_g)$-data, in the form of Katz–Mazur: the Hasse parameter $T$ trivialises the deformation ring, and $j - a_0$ is a unit times a distinguished polynomial in $T$ with the indicated coefficient valuations, valid for every prime $q$ (so not only the shape $P = X^k$ available for $q \ge 5$). It is used by the statements identifying the adic completion of the moduli ring at a supersingular point as a regular local ring with Hasse parameter, including the variant tracking the linear part of a problem automorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_coeff_nthSeries_sub_mul_mem_span_and_map_j0_sub_algebraMap_eq_mul_eval_of_factorsThrough_rigidDataH1Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.exists_coeff_nthSeries_sub_mul_mem_span_and_map_j0_sub_algebraMap_eq_mul_eval_of_factorsThrough_rigidDataH1Pow
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
    ∃ (T : R) (w : R) (_ : IsUnit w)
      (_ : PowerSeries.coeff q (F.nthSeries q) - w * T ∈ Ideal.span {(q : R)})
      (a₀ : W₀) (k : ℕ) (_ : 1 ≤ k) (w' : R) (_ : IsUnit w')

      (P : Polynomial W₀) (_ : P.Monic) (_ : P.natDegree = k)
      (_ : ∀ i < k, P.coeff i ∈ maximalIdeal W₀ ^ ((k - i) * q / (q + 1) + 1)),
      ι P₀.j₀ - algebraMap W₀ R a₀ = w' * (P.map (algebraMap W₀ R)).eval T := by sorry
