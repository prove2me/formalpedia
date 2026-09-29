-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_isBaseChange_and_isDrinfeldBasisAdic_residue_of_toPowerSeries_eq_gamma0Pow
-- name    : ModularCurve.LevelModuliPackageAbs.isBaseChange_and_isDrinfeldBasisAdic_residue_of_toPowerSeries_eq_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/98315138-7f2f-543e-a517-5277f264214d
-- title:
--   Residue base change of the universal formal group and Drinfeld-basis transport
-- statement:
--   Fix a prime $q \neq 2$, a prime $\ell \geq 3$, a natural number $M' \neq 0$ and a commutative ring $A₀$, together with: transport hypotheses `hℓ` and `hM` asserting that for every $A₀$-algebra $T$, [`ModularCurve.IsLevelPStructure`](def/ModularCurve_KatzLevelP.html#L104) at $\ell$ and [`ModularCurve.IsGamma0PowAt`](def/ModularCurve_WeierstrassGamma0Pow.html#L55) are preserved under a Weierstrass variable change $C$, the level data being moved by `LevelPData.variableChange` and by [`ModularCurve.kernelVariableChangeDeg`](def/ModularCurve_WeierstrassLevelComponents.html#L104) with degree [`ModularCurve.gamma0PowDeg`](def/ModularCurve_WeierstrassGamma0Pow.html#L53); a family of relative group laws $\mathcal{G}$ on projective Weierstrass models that is chord–tangent and has the origin as identity; a level transport $\mathcal{T}$ for $\mathcal{G}$ at $q$ satisfying `IsSectionTransport`; and a package $P₀$ with representing $A₀$-algebra $B₀$ and universal point `P₀.univ` for the moduli datum attached to `rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯`, whose level structure is the product of the $\Gamma_0$-power kernel component at the prime powers of $M'$, the level-$\ell$ component and the Drinfeld-pair component at $q$. Let $x$ be a raw point over $B₀$ (a Weierstrass curve with unit discriminant together with level data) whose class is `P₀.univ`. Let $R$ be a noetherian local $A₀$-algebra, complete for its maximal-ideal-adic topology, $\iota : B₀ \to R$ an $A₀$-algebra map, and $k$ a field of characteristic $q$ in which $\ell$ and $M'$ are nonzero, with $\mathrm{res}_R : R \to k$ surjective with kernel the maximal ideal. Let $W₀$ be a complete discrete valuation domain with maximal ideal $(q)$, residue map $\mathrm{res}_0$ onto $k$ with kernel the maximal ideal, with compatible $A₀ \to W₀ \to R$ scalar tower and $\mathrm{res}_R \circ \mathrm{algebraMap} = \mathrm{res}_0$; assume the factorisation property `hfac`: for every artinian local $W₀$- and $A₀$-algebra $T$ in the tower, with surjective residue map $\mathrm{res}_T$ to $k$ of kernel the maximal ideal and compatible with $\mathrm{res}_0$, and every $A₀$-algebra map $\varphi : B₀ \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R \circ \iota$, there is a unique $W₀$-algebra map $\Phi : R \to T$ with $\mathrm{res}_T \circ \Phi = \mathrm{res}_R$ and $\Phi \circ \iota = \varphi$. Write $E$ for the Weierstrass curve over $R$ carried by the Drinfeld-pair component of the level structure of the image of $x$ under $\iota$, and assume $E$ is elliptic. Finally let $F$ be a commutative formal group over $R$ whose two-variable power series is `E.formalGroupLawFixed`, and $F₀$ a commutative formal group over $k$ whose series is that of $E$ base changed along $\mathrm{res}_R$, such that $F₀$ satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. relative to the zero ideal the $q$-th $n$-series of $F₀$ is a unit multiple of its Drinfeld divisor at the parameters $0,0$. The conclusion is twofold: the series of $F₀$ is the coefficientwise image under $\mathrm{res}_R$ of that of $F$, and the formal group of $E$ base changed along the residue map of $R$ satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`. The proof uses only the two hypotheses identifying $F$ and $F₀$ with the formal group laws of $E$ and its reduction, the Drinfeld-basis hypothesis on $F₀$, the surjectivity and kernel of $\mathrm{res}_R$, and the ellipticity of $E$.
--
--   This is the reduction step identifying the formal group of the universal curve over the complete local base with a lift of the formal group of its reduction, and transferring the Drinfeld-basis condition from the chosen formal group over $k$ to the formal group of the reduced curve, stated for the $\Gamma_0(M')$-power level datum. It is invoked where the corresponding universal Drinfeld-basis statement over the base is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_isBaseChange_and_isDrinfeldBasisAdic_residue_of_toPowerSeries_eq_gamma0Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.isBaseChange_and_isDrinfeldBasisAdic_residue_of_toPowerSeries_eq_gamma0Pow
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
    [(((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).IsElliptic] :
    F.IsBaseChange resR F₀ ∧
      ((((rigidDataPow A₀ ℓ M' q hℓ hM 𝒢 𝒯).mapRing ι x).level.2.2.curve).map (IsLocalRing.residue R)).formalGroup.IsDrinfeldBasisAdic
        ⊥ q 0 0 := by sorry
