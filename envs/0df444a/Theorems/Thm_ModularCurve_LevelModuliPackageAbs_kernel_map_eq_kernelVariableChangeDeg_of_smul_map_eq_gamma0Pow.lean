-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_kernel_map_eq_kernelVariableChangeDeg_of_smul_map_eq_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.kernel_map_eq_kernelVariableChangeDeg_of_smul_map_eq_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/bd8306bf-6313-5cec-a18f-167d4951fdeb
-- title:
--   Uniqueness of Γ₀(M') kernel data under a trivial variable change
-- statement:
--   Fix a prime $q \neq 2$, a prime $\ell \geq 3$, a nonzero natural number $M'$ and a commutative ring $A_0$, together with two transport hypotheses: `hℓ`, that for every $A_0$-algebra $T$, Weierstrass curve $W$ over $T$, variable change $C$ and level-$P$ datum $D = (x_P,y_P,x_Q,y_Q)$, the conditions `IsLevelPStructure W ℓ D` (both points satisfy the affine equation, $\mathrm{pre}\Psi_\ell$ vanishes at $x_P$ and $x_Q$, and both independence elements are units) persist for $C \bullet W$ and $D.\mathrm{variableChange}\ C$; and `hM`, that `IsGamma0PowAt W p k h` persists for $C \bullet W$ and `kernelVariableChangeDeg C (gamma0PowDeg p k) h`. Let $\mathcal{G}$ be a family of relative group laws on the projective models of curves with unit discriminant, chord–tangent and with origin as identity, and $\mathcal{T}$ a level transport for $\mathcal{G}$ at $q$ satisfying `IsSectionTransport`; these assemble into the rigid Weierstrass datum `rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯`, whose raw points over an $A_0$-algebra consist of a Weierstrass curve with unit discriminant together with a family of monic-normalised kernel polynomials indexed by the prime factors of $M'$, a level-$\ell$ datum, and a Drinfeld pair of sections at $q$, all satisfying the corresponding `IsLevel` predicates. Let $P_0$ be a package representing the associated moduli datum: an $A_0$-algebra $B_0$ with a universal point `univ` such that every point over any $A_0$-algebra is induced by a unique $A_0$-algebra map out of $B_0$, and let $x$ be a raw datum over $B_0$ whose class is `univ`. Let $R$ be a noetherian local $A_0$-algebra, complete for its maximal ideal, with an $A_0$-algebra map $\iota : B_0 \to R$; let $k$ be a field of characteristic $q$ in which $\ell$ and $M'$ are invertible, $\mathrm{res}_R : R \to k$ surjective with kernel the maximal ideal; let $W_0$ be a complete discrete valuation ring with maximal ideal $(q)$ and residue map $\mathrm{res}_0$ onto $k$, with $R$ a $W_0$-algebra compatibly over $A_0$ and $\mathrm{res}_R$ extending $\mathrm{res}_0$. Assume the factorisation property `hfac`: for every artinian local $W_0$- and $A_0$-algebra $T$ with compatible surjection $\mathrm{res}_T$ onto $k$ with kernel the maximal ideal, every $A_0$-algebra map $\varphi : B_0 \to T$ lifting $\mathrm{res}_R \circ \iota$ extends to a unique $W_0$-algebra map $R \to T$ reducing to $\mathrm{res}_R$ and compatible with $\iota$. Let $F$ be a commutative formal group over $R$ given by the fixed formal group law of the Drinfeld-component curve of $\iota_* x$, $F_0$ the corresponding law over $k$ obtained from its reduction along $\mathrm{res}_R$, with $F_0$ a Drinfeld basis at $q$ with parameters $0,0$ for the zero ideal; let $\chi_P,\chi_Q$ be origin-chart homomorphisms to $R$ at which the two sections reduce to the origin modulo the maximal ideal, and assume $F$ is a Drinfeld basis at $q$ for the maximal ideal with parameters `originParam χP`, `originParam χQ`. Let $T$ be an artinian local $W_0$- and $A_0$-algebra with compatible surjection $\mathrm{res}_T$ onto $k$ of kernel the maximal ideal, $G$ a commutative formal group over $T$ obtained from $F_0$ by base change along $\mathrm{res}_T$, and $y_0,y_1$ in the maximal ideal of $T$ making $G$ a Drinfeld basis at $q$. Let $\varphi_1,\varphi_2 : R \to T$ be $W_0$-algebra maps, each reducing to $\mathrm{res}_R$ and each carrying $F$, via base change followed by an isomorphism of formal group laws onto $G$ whose series reduces to $X$, to $G$ in such a way that the adic evaluations of the isomorphism at the images of `originParam χP` and `originParam χQ` are $y_0$ and $y_1$. Finally let $C$ be a variable change over $T$ reducing to the identity modulo the maximal ideal with $C \bullet (\varphi_1 \circ \iota)_* x.\mathrm{curve} = (\varphi_2 \circ \iota)_* x.\mathrm{curve}$. The conclusion is that for every prime factor $p$ of $M'$ the $\Gamma_0$-component polynomial of $x$ at $p$, pushed forward along $\varphi_2 \circ \iota$, equals `kernelVariableChangeDeg C (gamma0PowDeg p (M'.factorization p))` applied to its pushforward along $\varphi_1 \circ \iota$.
--
--   This is the rigidity step for the cyclic-subgroup part of the level structure in the prime-power ($\Gamma_0(M')$) edition of the moduli datum: the kernel polynomials of two deformations related by a variable change congruent to the identity differ exactly by the action of that variable change, componentwise over the prime factors of $M'$ with the transport degree `gamma0PowDeg`. It feeds the comparison of the two induced points of the moduli problem in [`ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.map_univ_eq_of_isBaseChange_lawIso_appAdic_eq_gamma0Pow), via the unique-lifting property of $\Gamma_0$ kernel generators along surjections with nilpotent kernel.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_kernel_map_eq_kernelVariableChangeDeg_of_smul_map_eq_gamma0Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.kernel_map_eq_kernelVariableChangeDeg_of_smul_map_eq_gamma0Pow
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
    (C : WeierstrassCurve.VariableChange T) (hC : C.map resT = 1)
    (hCE : C • (x.curve.map (((φ₁.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom) = x.curve.map (((φ₂.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom) :
    ∀ pf : ↥M'.primeFactors,
      (x.level.1 pf).map (((φ₂.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom =
        ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg (pf : ℕ) (M'.factorization (pf : ℕ)))
          ((x.level.1 pf).map (((φ₁.restrictScalars A₀).comp ι) : P₀.B₀ →ₐ[A₀] T).toRingHom) := by sorry
