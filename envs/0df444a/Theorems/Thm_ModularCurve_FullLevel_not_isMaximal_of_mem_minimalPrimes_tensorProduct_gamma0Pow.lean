-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_not_isMaximal_of_mem_minimalPrimes_tensorProduct_gamma0Pow
-- name    : ModularCurve.FullLevel.not_isMaximal_of_mem_minimalPrimes_tensorProduct_gamma0Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:38.446507+00:00
-- url     : https://prove2.me/theorems/45c08e12-2c44-509c-a726-bfa2b822eda3
-- title:
--   No minimal prime of the generic fibre is maximal
-- statement:
--   Fix a prime $q\ge 5$, a nonzero $M'$ with $q\nmid M'$, and a prime $\ell\ge 3$ with $\ell\neq q$ and $\ell\nmid M'$. Let $L$ be a field of characteristic zero carrying a primitive $(q\ell)$-th root of unity $\xi$ and an embedding $\iota:L\to\mathbb C$ with $\iota(\xi)=e^{2\pi i/(q\ell)}$, let $K$ be the intermediate field of $L\subset L(\!(T)\!)$ obtained by adjoining to $L$ the image under coefficientwise extension $\mathbb Q\to L$ of the $q$-expansion function field of $\Gamma_H$ at level $(q\ell)^2M'$, where $H$ is the kernel of $(\mathbb Z/(q\ell)^2M')^\times\to(\mathbb Z/q\ell)^\times$, and let $j\in K$ be a nonzero element whose Laurent expansion is the image of the $q$-expansion of the modular invariant. Let $A$ be a discrete valuation domain with fraction field $L$, with $q$ in its maximal ideal and $\ell$, $M'$ units, and $K$ an $A$-algebra over $L$. Assume: variable changes preserve level-$\ell$ structures (equations for $P,Q$, vanishing of $\mathrm{pre}\Psi_\ell$, unit independence elements) and preserve the $\Gamma_0$-power kernel-polynomial condition; $\mathcal G$ is a family of relative group laws on projective models with unit discriminant which is chord-tangent and has the origin as identity; $\mathcal T$ is a level transport for $\mathcal G$ and $q$ on raw Drinfeld pairs which is a section transport; graded homomorphisms realising variable changes and coefficient maps exist on projective model rings. Let $P_0$ be a fine moduli package, i.e. an $A$-algebra $B_0$ of finite type with a universal point representing the moduli datum attached to $\mathrm{rigidDataPow}\,A\,\ell\,M'\,q$ (kernel polynomials at the primes of $M'$, a level-$\ell$ structure and a Drinfeld $q$-basis, modulo variable change). Then no minimal prime over $(0)$ in $L\otimes_A B_0$ is maximal.
--
--   The generic fibre of the fine moduli ring has no isolated point: every irreducible component of $\operatorname{Spec}(L\otimes_A B_0)$ has positive dimension, so no component consists of a single ($j$-constant) closed point. It is used in the identification of the image of the map from the moduli ring to the modular function field, via [`ModularCurve.FullLevel.comap_adjoin_jZero_eq_bot_of_mem_minimalPrimes_gamma0Pow`](thm.html#ModularCurve.FullLevel.comap_adjoin_jZero_eq_bot_of_mem_minimalPrimes_gamma0Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_not_isMaximal_of_mem_minimalPrimes_tensorProduct_gamma0Pow.lean

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
open scoped MatrixGroups TensorProduct

theorem ModularCurve.FullLevel.not_isMaximal_of_mem_minimalPrimes_tensorProduct_gamma0Pow
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

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
    [Algebra.FiniteType A P₀.B₀] :
    ∀ 𝔓 ∈ (⊥ : Ideal (L ⊗[A] P₀.B₀)).minimalPrimes, ¬ 𝔓.IsMaximal := by sorry
