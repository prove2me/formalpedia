-- Prove2me | Theorems.Thm_ModularCurve_LevelModuliPackageAbs_isBaseChange_and_isDrinfeldBasisAdic_residue_of_toPowerSeries_eq_rigidDataH1Pow
-- name    : ModularCurve.LevelModuliPackageAbs.isBaseChange_and_isDrinfeldBasisAdic_residue_of_toPowerSeries_eq_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/3a621e4f-eefc-5ace-b206-0ba00b1a8a2d
-- title:
--   Residue base change and Drinfeld basis of the reduced law
-- statement:
--   Fix a prime $q$, a prime $\ell_g$ with $\ell_g \equiv 11 \pmod{12}$, a natural number $M' \neq 0$ divisible by $\ell_g$, and a commutative ring $A_0$. Three equivariance hypotheses are assumed for all $A_0$-algebras $T$: `hℓ`, that `IsGamma1Point` at $\ell_g$ is preserved when a variable change $C$ acts on a Weierstrass curve and on the level data by `LevelPData.variableChange`; `hM`, that `IsGamma0PowAt` at $(p,k)$ is preserved when $C$ acts on the curve and on the kernel polynomial by `kernelVariableChangeDeg` in degree `gamma0PowDeg p k`; and `hL`, that a divisor of `inLineMulPoly W ℓg n x` is carried by `kernelVariableChangeDeg C d` to a divisor of the corresponding polynomial for $C \bullet W$ at the transformed abscissa. Let $\mathcal{G}$ be a family of relative group laws on the projective models of Weierstrass curves with invertible discriminant, assumed chord–tangent (`IsChordTangent`) and with the origin as identity in the origin chart (`IsOriginIdentity`), and $\mathcal{T}$ a level transport for $\mathcal{G}$ at $q$ satisfying `IsSectionTransport`. Let $P_0$ be a package representing, by the algebra $B_0$ with universal point `P₀.univ`, the moduli datum attached to the rigid Weierstrass datum `rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯`, and let $x$ be a raw datum over $B_0$ (a curve with invertible discriminant together with a $\Gamma_0(M')$-type tuple of kernel polynomials, a $\Gamma_1(\ell_g)$-type point, and a Drinfeld pair, satisfying the level conditions and the $\Gamma_1$-link divisibility) whose class is `P₀.univ`. Let $R$ be a noetherian local ring, complete for its maximal-ideal topology, an $A_0$-algebra, with an $A_0$-algebra map $\iota : B_0 \to R$; let $k$ be a field of characteristic $q$ in which $\ell_g$ and $M'$ are invertible, and $\mathrm{res}_R : R \to k$ a surjection with kernel the maximal ideal. Let $W_0$ be a complete discrete valuation domain with maximal ideal $(q)$ and residue map $\mathrm{res}_0 : W_0 \to k$ a surjection with kernel the maximal ideal, with $R$ a $W_0$-algebra compatibly over $A_0$ and $\mathrm{res}_R \circ (W_0 \to R) = \mathrm{res}_0$. A further hypothesis `hfac` asserts the expected universal property of $(R,\iota)$: for every artinian local $W_0$-algebra $T$ over $A_0$ with a surjection $\mathrm{res}_T : T \to k$ with kernel the maximal ideal, compatible with $\mathrm{res}_0$, every $A_0$-algebra map $\varphi : B_0 \to T$ with $\mathrm{res}_T \circ \varphi = \mathrm{res}_R \circ \iota$ factors through $R$ by a unique $W_0$-algebra map compatible with the residue maps. Write $E$ for the Weierstrass curve of the Drinfeld-pair component of the image of $x$ under $\iota$, assumed elliptic. Finally let $F$ be a commutative formal group over $R$ whose power series is `E.formalGroupLawFixed`, and $F_0$ a commutative formal group over $k$ whose power series is that of $E$ reduced along $\mathrm{res}_R$, such that $F_0$ satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`, i.e. the $q$-th series `F₀.nthSeries q` is a unit multiple of the Drinfeld divisor `F₀.drinfeldDivisor q 0 0` with respect to the zero ideal. The conclusion is twofold: $F_0$ is the base change of $F$ along $\mathrm{res}_R$, in the sense that the power series of $F_0$ is the image of that of $F$ under `MvPowerSeries.map resR`; and the formal group of $E$ reduced along the canonical residue map $R \to$ `ResidueField R` again satisfies `IsDrinfeldBasisAdic ⊥ q 0 0`.
--
--   This is the compatibility step which says that the formal group of the universal curve over the complete local ring $R$ reduces, along the residue map, to the formal group of the reduced curve, and that the Drinfeld-basis condition at level $q$ for $(0,0)$ descends to the residue field, formulated intrinsically for the residue field of $R$ rather than for the chosen quotient $k$. It feeds the construction of a universal point with a Drinfeld basis reducing to the origin, [`ModularCurve.LevelModuliPackageAbs.exists_reducesToOrigin_isDrinfeldBasisAdic_universal_of_factorsThrough_rigidDataH1Pow`](thm.html#ModularCurve.LevelModuliPackageAbs.exists_reducesToOrigin_isDrinfeldBasisAdic_universal_of_factorsThrough_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelModuliPackageAbs_isBaseChange_and_isDrinfeldBasisAdic_residue_of_toPowerSeries_eq_rigidDataH1Pow.lean

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

theorem ModularCurve.LevelModuliPackageAbs.isBaseChange_and_isDrinfeldBasisAdic_residue_of_toPowerSeries_eq_rigidDataH1Pow
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
    [(((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).IsElliptic] :
    F.IsBaseChange resR F₀ ∧
      ((((rigidDataH1Pow A₀ ℓg M' q hℓ hM hL 𝒢 𝒯).mapRing ι x).level.2.2.curve).map (IsLocalRing.residue R)).formalGroup.IsDrinfeldBasisAdic
        ⊥ q 0 0 := by sorry
