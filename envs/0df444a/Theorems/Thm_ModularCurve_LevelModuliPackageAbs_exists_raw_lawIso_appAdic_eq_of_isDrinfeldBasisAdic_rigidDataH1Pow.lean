-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_exists_raw_lawIso_appAdic_eq_of_isDrinfeldBasisAdic_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.exists_raw_lawIso_appAdic_eq_of_isDrinfeldBasisAdic_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/6852e11c-786d-5db4-b9ce-a56a4e461a7e
-- title:
--   Artinian lift of a Drinfeld basis to a raw H₁ datum
-- statement:
--   Fix a prime $q$, a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$, and a nonzero $M'$ divisible by $\ell_g$, together with a commutative ring $A_0$ and three variable-change compatibility hypotheses over $A_0$-algebras: `hℓ`, that the $\Gamma_1(\ell_g)$-point condition is preserved by the action of a variable change on level-$p$ data; `hM`, that the condition `IsGamma0PowAt` for $(p,k)$ is preserved when the kernel polynomial is transformed by `kernelVariableChangeDeg` in degree `gamma0PowDeg p k`; and `hL`, that divisibility of `inLineMulPoly` is preserved under the same transformations. Let $\mathcal{G}$ be a family of relative group laws on projective Weierstrass models with unit discriminant which is chord-tangent and has the origin as identity section, and $\mathcal{T}$ a level transport for Drinfeld $\Gamma(q)$-pairs satisfying the section-transport compatibilities. Write $\mathcal{R} =$ `rigidDataH1Pow` $A_0\,\ell_g\,M'\,q$ for the rigid Weierstrass datum whose level object over $T$ is a triple consisting of a family of polynomials indexed by the prime factors $p$ of $M'$ generating cyclic $p^{v_p(M')}$-kernels, a $\Gamma_1(\ell_g)$-point datum, and a Drinfeld pair, subject additionally to the link condition that the polynomial at $\ell_g$ divides `inLineMulPoly` at the $x$-coordinate of the $\Gamma_1$-point. Let $P_0$ be a package representing the associated moduli datum, with algebra $B_0$ and universal point, and let $x$ be a raw datum over $B_0$ whose class is that universal point. Let $R$ be a noetherian local $A_0$-algebra, complete for its maximal ideal, $\iota : B_0 \to R$ an $A_0$-algebra map, $k$ a field of characteristic $q$ in which $\ell_g$ and $M'$ are invertible, $\mathrm{res}_R : R \to k$ surjective with kernel the maximal ideal, and $W_0$ a complete discrete valuation domain with maximal ideal $(q)$ and surjective residue map $\mathrm{res}_0 : W_0 \to k$ with kernel the maximal ideal; $R$ is a $W_0$-algebra, the tower $A_0 \to W_0 \to R$ commutes, and $\mathrm{res}_R$ restricts to $\mathrm{res}_0$ on $W_0$. Assume the factorisation property `hfac`: for every artinian local ring $T$ that is a $W_0$- and $A_0$-algebra compatibly, with surjective residue map $\mathrm{res}_T$ onto $k$ with kernel the maximal ideal and extending $\mathrm{res}_0$, and every $A_0$-algebra map $\varphi : B_0 \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R \circ \iota$, there is a unique $W_0$-algebra map $\Phi : R \to T$ compatible with the residue maps and with $\Phi \circ \iota = \varphi$. Let $F$ be a commutative formal group over $R$ whose power series is the normalised Weierstrass formal group law of the curve carried by the Drinfeld-pair component of $\mathcal{R}.\mathrm{mapRing}\,\iota\,x$, let $F_0$ over $k$ be the corresponding law of the reduction of that curve along $\mathrm{res}_R$, assumed to be a Drinfeld basis for $q$ at the parameters $0,0$ relative to the zero ideal, let $\chi_P, \chi_Q$ be ring homomorphisms from the origin chart ring of that curve to $R$ through which the sections $P$ and $Q$ reduce to the origin modulo the maximal ideal, and assume $F$ is a Drinfeld basis for $q$ at `originParam` $\chi_P$ and `originParam` $\chi_Q$ relative to the maximal ideal of $R$. Finally let $T$ be an artinian local $W_0$- and $A_0$-algebra with compatible surjective residue map $\mathrm{res}_T$ onto $k$ extending $\mathrm{res}_0$, let $G$ be a commutative formal group over $T$ obtained from $F_0$ by base change along $\mathrm{res}_T$, and let $y_0, y_1$ lie in the maximal ideal of $T$ and form a Drinfeld basis for $G$ and $q$ relative to that ideal. The conclusion asserts the existence of a raw datum $y_T$ for $\mathcal{R}$ over $T$, ring homomorphisms $\chi_{P,T}, \chi_{Q,T}$ from the origin chart ring of the curve of its Drinfeld-pair component to $T$, a formal group $G_T$ over $T$ whose power series is the normalised Weierstrass law of that curve, and an isomorphism $\psi$ of formal group laws from $G_T$ to $G$, such that the coefficients of $\psi$ reduce along $\mathrm{res}_T$ to those of $X$ (the $n$-th coefficient maps to $1$ for $n = 1$ and to $0$ otherwise), the two sections of $y_T$ reduce to the origin through $\chi_{P,T}$ and $\chi_{Q,T}$, the adic evaluation of $\psi$ sends `originParam` $\chi_{P,T}$ to $y_0$ and `originParam` $\chi_{Q,T}$ to $y_1$, and the reductions along $\mathrm{res}_T$ of the curve of $y_T$, of its $\Gamma_1(\ell_g)$-point datum, and of each of its kernel polynomials indexed by the prime factors of $M'$ agree with the reductions along $\mathrm{res}_R$ of the corresponding data of $\mathcal{R}.\mathrm{mapRing}\,\iota\,x$.
--
--   This is the gluing step that converts an Artinian-level formal group with a prescribed Drinfeld $\Gamma(q)$-basis into an actual point of the moduli problem of level $\Gamma_0(M') \cap \Gamma_1(\ell_g)$ with Drinfeld $\Gamma(q)$-structure, lifting the given data from the residue field $k$ to the Artinian base $T$ together with a $\star$-isomorphism of formal group laws that reduces to the identity. It is used to produce the algebra map out of the representing object in [`ModularCurve.LevelModuliPackageAbs.exists_algHom_isBaseChange_lawIso_appAdic_eq_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_algHom_isBaseChange_lawIso_appAdic_eq_rigidDataH1Pow), which identifies deformations of the reduction with points of the moduli package.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_exists_raw_lawIso_appAdic_eq_of_isDrinfeldBasisAdic_rigidDataH1Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.exists_raw_lawIso_appAdic_eq_of_isDrinfeldBasisAdic_rigidDataH1Pow
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
    (G : FormalGroup T) [G.IsComm] (hG : G.IsBaseChange resT F₀)
    (y₀ y₁ : T) (hy₀ : y₀ ∈ maximalIdeal T) (hy₁ : y₁ ∈ maximalIdeal T)
    (hDy : G.IsDrinfeldBasisAdic (maximalIdeal T) q y₀ y₁)
    :
    ∃ (yT : (rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).Raw T)
      (χPT χQT : OriginChartRing yT.level.2.2.curve →+* T)
      (GT : FormalGroup T) (_ : GT.toPowerSeries = yT.level.2.2.curve.formalGroupLawFixed)
      (ψ : FormalGroup.LawIso GT G),
      (∀ n : ℕ, resT (PowerSeries.coeff n ψ.series) = if n = 1 then 1 else 0) ∧
      ReducesToOrigin yT.level.2.2.P χPT (maximalIdeal T) ∧ ReducesToOrigin yT.level.2.2.Q χQT (maximalIdeal T) ∧
      ψ.toLawHom.appAdic (maximalIdeal T) (originParam χPT) = y₀ ∧
      ψ.toLawHom.appAdic (maximalIdeal T) (originParam χQT) = y₁ ∧

      yT.curve.map resT = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR ∧
      yT.level.2.1.map resT = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.1).map resR ∧
      (∀ pf : ↥M'.primeFactors, (yT.level.1 pf).map resT = (((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.1 pf).map resR) := by sorry
