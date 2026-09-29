-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_exists_algHom_dualNumber_fst_eq_snd_ne_zero_gamma0Pow
-- name    : ModularCurve.FullLevel.exists_algHom_dualNumber_fst_eq_snd_ne_zero_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:33.630704+00:00
-- url     : https://prove2.me/theorems/17c4ef90-a6c1-5272-bc16-ebd1018db2f2
-- title:
--   Every Ω-point of the full-level moduli ring has a tangent vector
-- statement:
--   Fix a prime $q \ge 5$, a nonzero natural number $M'$ not divisible by $q$, and a prime $\ell \ge 3$ with $\ell \ne q$ and $\ell \nmid M'$; let $A$ be a commutative ring in which $\ell$ and $M'$ are invertible. Assume: the variable-change equivariance statements `hℓ` (if $(x_P,y_P,x_Q,y_Q)$ is a level-$\ell$ datum for $W$ over an $A$-algebra, meaning both points satisfy the affine Weierstrass equation, $\mathrm{pre}\Psi_\ell$ vanishes at both $x$-coordinates and both independence elements $\mathrm{indepElt}$ are units, then its transform under a variable change $C$ is such a datum for $C \bullet W$) and `hM` (the predicate `IsGamma0PowAt`, i.e. `IsTwoKernel` when $p^k = 2$ and otherwise `IsCyclicGenKernel`, is preserved by `kernelVariableChangeDeg`); a family $\mathcal G$ of relative group laws on the graded Proj models of projective Weierstrass curves with unit discriminant over $A$-algebras, satisfying `IsChordTangent` (existence of a points-evaluation bijection additive and Galois-equivariant over fields) and `IsOriginIdentity` (the unit section is the origin chart section killing $x/y$ and $z/y$); a level transport $\mathcal T$ for raw Drinfeld pairs at $q$, functorial in $A$-algebra maps and equivariant for variable changes, preserving the condition that $(P,Q)$ is a Drinfeld basis of level $q$, together with `IsSectionTransport`; and the hypotheses `hVC`, `hCO` providing graded ring homomorphisms between the graded coordinate rings of projective models that realise variable changes, respectively coefficient maps, and pull back the irrelevant ideal appropriately. Let $P_0$ be a fine moduli package for the level moduli datum of the rigid Weierstrass data `rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯` (the product of the $\Gamma_0(p^{k})$-kernel-polynomial component at the prime powers of $M'$, the level-$\ell$ component and the Drinfeld level-$q$ component), so $P_0$ consists of an $A$-algebra $B_0$ with a universal point which represents the functor of points. Finally let $\Omega$ be an algebraically closed field of characteristic zero which is an $A$-algebra with $q \ne 0$ in $\Omega$, and let $\varphi_0 : B_0 \to \Omega$ be an $A$-algebra map. Then there exists an $A$-algebra map $\varphi : B_0 \to \Omega[\varepsilon]/(\varepsilon^2)$ whose first component is $\varphi_0$ on every element, and such that the $\varepsilon$-component of $\varphi(b)$ is nonzero for at least one $b \in B_0$.
--
--   The assertion is that no $\Omega$-point of the fine moduli ring $B_0$ of elliptic curves with full rigid level structure (Drinfeld level $q$, level $\ell$, and $\Gamma_0$-kernel data at the prime powers of $M'$) is an isolated point: each such point carries a nontrivial tangent vector, coming from a first-order deformation of the corresponding curve with its level data. It is used in the proof that minimal primes of the relevant tensor product are not maximal ideals, a step towards the absence of isolated generic points of the moduli ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_exists_algHom_dualNumber_fst_eq_snd_ne_zero_gamma0Pow.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.exists_algHom_dualNumber_fst_eq_snd_ne_zero_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (A : Type) [CommRing A]
    (hℓA : IsUnit ((ℓ : ℕ) : A)) (hM'A : IsUnit ((M' : ℕ) : A))
    (hℓ : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (D : ModularCurve.LevelPData T), ModularCurve.IsLevelPStructure W ℓ D →
        ModularCurve.IsLevelPStructure (C • W) ℓ (D.variableChange C))
    (hM : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
      (p k : ℕ) (h : Polynomial T), ModularCurve.IsGamma0PowAt W p k h →
        ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h))
    (𝒢 : GroupLaws A) (h𝒢 : 𝒢.IsChordTangent) (h𝒢O : 𝒢.IsOriginIdentity)
    (𝒯 : LevelTransport A 𝒢 q) (h𝒯 : 𝒯.IsSectionTransport)
    (hVC : ∀ (T : Type) [CommRing T] [Algebra A T] (W : WeierstrassCurve.Projective T) (C : WeierstrassCurve.VariableChange T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (C • W))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (C • W)) ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsVariableChangeHom W C φ)
    (hCO : ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T')
      (W : WeierstrassCurve.Projective T),
      ∃ (φ : projModelGradingCR W →+*ᵍ projModelGradingCR (W.map f.toRingHom))
        (_ : HomogeneousIdeal.irrelevant (projModelGradingCR (W.map f.toRingHom)) ≤
          (HomogeneousIdeal.irrelevant (projModelGradingCR W)).map φ),
        IsCoefficientHom W f.toRingHom φ)
    (P₀ : LevelModuliPackageAbs A (rigidDataPow A ℓ M' q hℓ hM 𝒢 𝒯).toLevelModuliDatum)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Algebra A Ω] (hqΩ : ((q : ℕ) : Ω) ≠ 0)
    (φ₀ : P₀.B₀ →ₐ[A] Ω) :
    ∃ φ : P₀.B₀ →ₐ[A] DualNumber Ω,
      (∀ b : P₀.B₀, (φ b).fst = φ₀ b) ∧ ∃ b : P₀.B₀, (φ b).snd ≠ 0 := by sorry
