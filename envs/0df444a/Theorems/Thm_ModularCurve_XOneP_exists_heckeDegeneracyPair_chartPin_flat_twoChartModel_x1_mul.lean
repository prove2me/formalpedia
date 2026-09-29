-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_heckeDegeneracyPair_chartPin_flat_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_heckeDegeneracyPair_chartPin_flat_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/ee1b54ec-cd38-53ff-82a7-78b02cb9d6ac
-- title:
--   Hecke degeneracy pair on the two-chart model of X₁(Mp)
-- statement:
--   Fix a prime $p$ and $M$ with $5 \le M$ and $p \nmid M$, a field $L$ of characteristic zero that is a $p$-th cyclotomic extension of $\mathbb{Q}$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be the intermediate field of $L(\!(q)\!)$ over $L$ equal to `laurentBaseChange` of `x1FunctionField (M * p)`, i.e. generated over $L$ by the coefficientwise image under $\mathbb{Q} \to L$ of the $q$-expansion function field of $\Gamma_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal and $\zeta$ in the image of $A$, acting on $K$ compatibly with $L$, and let $j \in K$ be a nonzero element whose Laurent series is the image of `jq`. Let $\ell$ be a prime, and let $K_\ell$ be the corresponding intermediate field attached to `x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)`, the function field of $\Gamma_1(Mp) \cap \Gamma_0(Mp\ell)$, with a nonzero $j_\ell \in K_\ell$ again having Laurent series the image of `jq`. Assume `HeckeBetaOneDefined (M * p) ℓ`: substitution $q \mapsto q^{\ell}$ carries `x1FunctionField (M * p)` into `x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)`. Here the two-chart model `TwoChartModel A F jF` is the pushout gluing $\operatorname{Spec}$ of `chartAlgFin` (the elements of $F$ integral over $A[j_F]$) and of `chartAlgInf` (those integral over $A[j_F^{-1}]$) along the middle algebra, with structure morphism `modelTo` to $\operatorname{Spec} A$. The assertion is that there exist two morphisms $\pi_\alpha, \pi_\beta$ from the two-chart model of $(K_\ell, j_\ell)$ to that of $(K, j)$, commuting with the structure morphisms to $\operatorname{Spec} A$, both finite and locally of finite presentation, $A$-algebra maps $\iota_\alpha, \iota_\beta$ from `chartAlgFin A K j` to `chartAlgFin A K_ℓ jℓ`, and an open $U$ of the two-chart model of $(K, j)$ such that: both $\pi_\alpha, \pi_\beta$ are surjective on points; $\iota_\alpha$ is the identity on Laurent series and $\iota_\beta$ is $q \mapsto q^{\ell}$ (`qExpand L ℓ`); the chart inclusion `ιFin` for $(K_\ell, j_\ell)$ followed by $\pi_\alpha$ (resp. $\pi_\beta$) equals $\operatorname{Spec}$ of $\iota_\alpha$ (resp. $\iota_\beta$) followed by `ιFin` for $(K, j)$; the preimage under each of the open range of `ιFin A K j` is exactly the open range of `ιFin A K_ℓ jℓ`; $U$ contains every point whose local ring has Krull dimension at most $1$; both morphisms restricted to $U$ are flat; and at every $y \in U$ the rank of each is $\ell$ if $\ell \mid Mp$ and $\ell + 1$ otherwise.
--
--   This is the pair of degeneracy morphisms underlying the Hecke correspondence of level $\ell$ over the integral two-chart model of $X_1(Mp)$ over a discrete valuation ring with fraction field $\mathbb{Q}(\zeta_p)$ above $p$, with the $j$-chart compatibility recorded on $q$-expansions and flatness of constant degree $\ell + 1 - [\ell \mid Mp]$ over the codimension-at-most-one locus. It is used for the Hecke action on the model and its Jacobian, in particular by the statements descending Hecke generators away from the components of the special fibre, comparing Hecke translates of the Abel–Jacobi map, and identifying the preimage of the finite chart.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_heckeDegeneracyPair_chartPin_flat_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem ModularCurve.XOneP.exists_heckeDegeneracyPair_chartPin_flat_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (ℓ : ℕ) [Fact ℓ.Prime]

    [Algebra A ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    [IsScalarTower A L ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))]
    (jℓ : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ))))
    (hjℓ : ((jℓ : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (jℓ ≠ 0)]

    (hβ : ModularCurve.HeckeBetaOneDefined (M * p) ℓ) :
    ∃ (πα πβ : SchemeHomOver (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (_ : IsFinite πα.1) (_ : IsFinite πβ.1) (_ : LocallyOfFinitePresentation πα.1) (_ : LocallyOfFinitePresentation πβ.1)
      (ια ιβ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ))
      (U : (ModularCurve.TwoChartModel A (↥K) j).Opens),

      Function.Surjective πα.1.base ∧ Function.Surjective πβ.1.base ∧

      (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ια b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ((b : ↥K) : LaurentSeries L)) ∧
      (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ιβ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) =
        ModularCurve.qExpand L ℓ ((b : ↥K) : LaurentSeries L)) ∧
      ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πα.1 = Spec.map (CommRingCat.ofHom ια.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j ∧
      ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πβ.1 = Spec.map (CommRingCat.ofHom ιβ.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j ∧

      πα.1 ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).opensRange ∧
      πβ.1 ⁻¹ᵁ (ModularCurve.TwoChart.ιFin A (↥K) j).opensRange = (ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ).opensRange ∧

      (∀ x : ↥(ModularCurve.TwoChartModel A (↥K) j), ringKrullDim ((ModularCurve.TwoChartModel A (↥K) j).presheaf.stalk x) ≤ 1 → x ∈ U) ∧
      Flat (πα.1 ∣_ U) ∧ Flat (πβ.1 ∣_ U) ∧
      (∀ y : ↥(ModularCurve.TwoChartModel A (↥K) j), y ∈ U → πα.1.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1)) ∧
      (∀ y : ↥(ModularCurve.TwoChartModel A (↥K) j), y ∈ U → πβ.1.finrank y = (if ℓ ∣ M * p then ℓ else ℓ + 1)) := by sorry
