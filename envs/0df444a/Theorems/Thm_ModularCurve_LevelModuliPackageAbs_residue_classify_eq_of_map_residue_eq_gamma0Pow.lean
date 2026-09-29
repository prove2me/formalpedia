-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_residue_classify_eq_of_map_residue_eq_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.residue_classify_eq_of_map_residue_eq_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/b541d876-238f-55dd-8928-3d204c35c982
-- title:
--   Residue compatibility of the classifying map at Γ₀-power level
-- statement:
--   Fix a prime $q \neq 2$, a prime $\ell \geq 3$, a natural number $M' \neq 0$ and a commutative ring $A₀$, together with two transport hypotheses: `hℓ`, that over any $A₀$-algebra a level-$\ell$ datum $D$ (four coordinates $x_P,y_P,x_Q,y_Q$ satisfying the `IsLevelPStructure` conditions for $\ell$) stays such after a variable change $C$, and `hM`, that `IsGamma0PowAt W p k h` is preserved when $W$ is replaced by $C \bullet W$ and $h$ by `kernelVariableChangeDeg C (gamma0PowDeg p k) h`. Let $\mathcal{G}$ be a family of relative group laws on the projective models of curves with unit discriminant, assumed chord-tangent and origin-identity, and $\mathcal{T}$ a level transport for $\mathcal{G}$ and $q$ satisfying `IsSectionTransport`. Let $P₀$ be an absolute representing package for the moduli datum of `rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯`, whose raw objects over $T$ consist of a Weierstrass curve with unit discriminant together with a $\Gamma_0$-slot (a kernel generator polynomial `IsGamma0PowAt` for each prime factor $p$ of $M'$ at exponent $v_p(M')$), a level-$\ell$ datum, and a raw Drinfeld pair $(P,Q)$ forming a Drinfeld $q$-basis for $\mathcal{G}$; let $x$ be a raw object over $P₀.B₀$ whose class is the universal point $P₀.univ$. Let $R$ be a Noetherian local $A₀$-algebra, complete for its maximal ideal, with an $A₀$-algebra map $\iota : P₀.B₀ \to R$, let $k$ be a field of characteristic $q$ in which $\ell$ and $M'$ are invertible, and $resR : R \to k$ a surjection with kernel the maximal ideal. Let $W₀$ be a complete discrete valuation domain with maximal ideal $(q)$ and residue map $res₀$ onto $k$, with $A₀ \to W₀ \to R$ a scalar tower and $resR$ compatible with $res₀$. Assume the factorisation property `hfac`: for every Artinian local $W₀$-algebra $T$ in the tower, with a surjection $resT : T \to k$ of kernel the maximal ideal compatible with $res₀$, and every $A₀$-algebra map $\varphi : P₀.B₀ \to T$ with $resT \circ \varphi = resR \circ \iota$, there is a unique $W₀$-algebra map $\Phi : R \to T$ with $resT \circ \Phi = resR$ and $\Phi \circ \iota = \varphi$. Assume further: a commutative formal group $F$ over $R$ whose power series is the fixed formal group law of the Drinfeld-slot curve of `mapRing ι x`; a commutative formal group $F₀$ over $k$ whose power series is that of the $resR$-reduction of the same curve, with `F₀.IsDrinfeldBasisAdic ⊥ q 0 0`; origin charts $\chi_P, \chi_Q$ for which the sections $P$ and $Q$ of that curve reduce to the origin modulo the maximal ideal of $R$; and that $F$ is a Drinfeld $q$-basis, adically for the maximal ideal of $R$, at the origin parameters of $\chi_P$ and $\chi_Q$. Then, for any Artinian local $T$ as in `hfac` with residue map $resT$, any raw object $y_T$ over $T$ whose Drinfeld sections reduce to the origin via charts $\chi_{P,T}, \chi_{Q,T}$, and whose curve, level-$\ell$ datum and $\Gamma_0$-kernel polynomials (the last pointwise over the prime factors of $M'$) have the same reductions to $k$ along $resT$ as those of `mapRing ι x` along $resR$, the classifying map of the class of $y_T$ satisfies $resT(P₀.\mathrm{classify}\,[y_T]\,b) = resR(\iota\,b)$ for every $b \in P₀.B₀$.
--
--   This is the residue-compatibility step for the universal deformation description of the moduli problem $\Gamma_0(M') \times \Gamma(\ell) \times \Gamma_{\mathrm{Drinfeld}}(q)$ in the prime-power $\Gamma_0$ formulation, where the $\Gamma_0$-level is recorded by one kernel generator polynomial for each prime factor of $M'$. It supplies the hypothesis needed to produce, from a test object whose invariants agree modulo the maximal ideal, an algebra map out of the complete local ring $R$, and is used in [`ModularCurve.LevelModuliPackageAbs.exists_algHom_of_raw_lawIso_appAdic_eq_gamma0Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_algHom_of_raw_lawIso_appAdic_eq_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_residue_classify_eq_of_map_residue_eq_gamma0Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.residue_classify_eq_of_map_residue_eq_gamma0Pow
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
    (yT : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Raw T)
    (χPT χQT : OriginChartRing yT.level.2.2.curve →+* T)
    (hPT : ReducesToOrigin yT.level.2.2.P χPT (maximalIdeal T))
    (hQT : ReducesToOrigin yT.level.2.2.Q χQT (maximalIdeal T))
    (hcurve : yT.curve.map resT = (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).map resR)
    (hlev : yT.level.2.1.map resT = (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.1).map resR)
    (hker : (∀ pf : ↥M'.primeFactors, (yT.level.1 pf).map resT = (((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.1 pf).map resR)) :
    ∀ b : P₀.B₀,
      resT (P₀.classify (Quot.mk _ yT : (rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).Pt T) b) = resR (ι b) := by sorry
