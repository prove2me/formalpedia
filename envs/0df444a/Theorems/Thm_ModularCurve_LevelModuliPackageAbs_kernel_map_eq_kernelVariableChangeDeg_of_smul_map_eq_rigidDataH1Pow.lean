-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_kernel_map_eq_kernelVariableChangeDeg_of_smul_map_eq_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.kernel_map_eq_kernelVariableChangeDeg_of_smul_map_eq_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/a4106526-a2ab-5191-9e1b-69a4b1dbbdb9
-- title:
--   Kernel data of two lifts differ by the variable change
-- statement:
--   Fix a prime $q$, natural numbers $\ell_g$ and $M'$ with $\ell_g$ prime, $\ell_g \equiv 11 \pmod{12}$, $M' \neq 0$ and $\ell_g \mid M'$, and a commutative ring $A_0$. Three equivariance hypotheses are assumed for all $A_0$-algebras: $h\ell$, that a $\Gamma_1(\ell_g)$-point datum (a quadruple $x_P,y_P,x_Q,y_Q$ with $(x_P,y_P)$ on the curve, $(W.\mathrm{pre}\Psi\,\ell_g)(x_P)=0$ and $x_Q=x_P$, $y_Q=y_P$) is carried by a variable change $C$ to such a datum for $C \bullet W$; $hM$, that `IsGamma0PowAt` for $(p,k)$ is preserved by `kernelVariableChangeDeg C (gamma0PowDeg p k)`, where $\mathrm{gamma0PowDeg}\,p\,k$ is $1$ if $p^k=2$ and $\varphi(p^k)/2$ otherwise, and $\mathrm{kernelVariableChangeDeg}\,C\,d\,h = u^{-2d}\,h(u^{2}X+r)$; and $hL$, the corresponding divisibility statement for `inLineMulPoly`. Further data: group laws $\mathcal{G}$ on projective Weierstrass models which are chord–tangent and origin-identity, a level transport $\mathcal{T}$ for Drinfeld $\Gamma(q)$-bases satisfying `IsSectionTransport`, and a representing object $P_0$ (carrier $B_0$, universal point, uniqueness of classifying maps) for the moduli datum of `rigidDataH1Pow`, whose raw objects consist of a Weierstrass curve with unit discriminant together with a tuple of prime-power kernel polynomials indexed by the prime factors of $M'$, a $\Gamma_1(\ell_g)$-point datum, a Drinfeld $\Gamma(q)$-basis pair, and the link condition that the $\ell_g$-component divides $\mathrm{inLineMulPoly}$ at $x_P$. Let $x$ be a raw object over $B_0$ whose class is the universal point. Let $R$ be a complete Noetherian local $A_0$-algebra with residue map $\mathrm{res}_R$ onto a field $k$ of characteristic $q$ in which $\ell_g$ and $M'$ are nonzero, $\iota : B_0 \to R$ an $A_0$-algebra map, and $W_0$ a complete discrete valuation ring with maximal ideal $(q)$ and residue field $k$, with $R$ a $W_0$-algebra compatibly over $A_0$; $hfac$ asserts that $R$ has the universal property that for every Artinian local $W_0$-algebra $T$ with residue map to $k$ and every $A_0$-algebra map $\varphi : B_0 \to T$ lifting $\mathrm{res}_R \circ \iota$ there is a unique $W_0$-algebra map $R \to T$ compatible with the residue maps and with $\varphi$ on $\iota(B_0)$. Let $F$ be a commutative formal group over $R$ whose power series is the fixed formal group law of the curve of $(\mathrm{mapRing}\,\iota)\,x$, $F_0$ the corresponding object over $k$ for the reduced curve, $F_0$ a Drinfeld basis at the zero ideal with parameters $0,0$; let $\chi_P,\chi_Q$ be origin-chart ring homomorphisms to $R$ along which the two Drinfeld sections reduce to the origin, and let $F$ be a Drinfeld basis for the maximal ideal of $R$ with parameters $\mathrm{originParam}\,\chi_P$, $\mathrm{originParam}\,\chi_Q$. Finally let $T$ be an Artinian local $W_0$-algebra with residue map to $k$ as above, $G$ a commutative formal group over $T$ obtained from $F_0$ by base change along $\mathrm{res}_T$, admitting a Drinfeld basis $y_0,y_1$ in the maximal ideal, and let $\varphi_1,\varphi_2 : R \to T$ be $W_0$-algebra maps each compatible with the residue maps and each equipped with a base change of $F$ and an isomorphism of that base change with $G$ whose series reduces to $X$ and which sends the images of $\mathrm{originParam}\,\chi_P$, $\mathrm{originParam}\,\chi_Q$ to $y_0$, $y_1$. If $C$ is a variable change over $T$ reducing to the identity under $\mathrm{res}_T$ and carrying the curve of $x$ pushed forward along $\varphi_1 \circ \iota$ to the one pushed forward along $\varphi_2 \circ \iota$, then for every prime factor $pf$ of $M'$ the $pf$-component kernel polynomial of $x$ pushed forward along $\varphi_2 \circ \iota$ equals $\mathrm{kernelVariableChangeDeg}\,C\,(\mathrm{gamma0PowDeg}\,pf\,(\mathrm{ord}_{pf}M'))$ applied to the same polynomial pushed forward along $\varphi_1 \circ \iota$.
--
--   This is the rigidity step for the $\Gamma_0(M')$-part of the level structure: two lifts of the same residual situation whose curves differ by a variable change trivial modulo the maximal ideal have kernel data differing exactly by the induced action of that variable change, because a prime-power cyclic kernel generator lifting a given one over the residue ring is unique. It feeds into [`ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_rigidDataH1Pow), where the two classifying maps $\varphi_1,\varphi_2$ are shown to agree, i.e. into the representability argument for the deformation problem with $\Gamma_0(M') \cap \Gamma_1(\ell_g)$ and Drinfeld $\Gamma(q)$ level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_kernel_map_eq_kernelVariableChangeDeg_of_smul_map_eq_rigidDataH1Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.kernel_map_eq_kernelVariableChangeDeg_of_smul_map_eq_rigidDataH1Pow
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
    (C : WeierstrassCurve.VariableChange T) (hC : C.map resT = 1)
    (hCE : C • (x.curve.map (((φ₁.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom) = x.curve.map (((φ₂.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom) :
    ∀ pf : ↥M'.primeFactors,
      (x.level.1 pf).map (((φ₂.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom =
        ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (pf : ℕ) (M'.factorization (pf : ℕ)))
          ((x.level.1 pf).map (((φ₁.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom) := by sorry
