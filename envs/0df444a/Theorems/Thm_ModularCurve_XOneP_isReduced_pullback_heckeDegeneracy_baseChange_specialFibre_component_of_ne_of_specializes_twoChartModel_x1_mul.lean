-- Prove2me | Theorems.Thm_ModularCurve_XOneP_isReduced_pullback_heckeDegeneracy_baseChange_specialFibre_component_of_ne_of_specializes_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.isReduced_pullback_heckeDegeneracy_baseChange_specialFibre_component_of_ne_of_specializes_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/263b5993-57dc-53d8-ba5f-a4e5c932ce02
-- title:
--   Reducedness of a special-fibre component's preimage under π_α, ℓ≠ p
-- statement:
--   Fix a prime $p$, an integer $M\neq 0$ with $5\le M$ and $p\nmid M$, a field $L$ of characteristic zero that is a $p$-cyclotomic extension of $\mathbb{Q}$, and a primitive $p$-th root of unity $\zeta\in L$. Let $K$ be an intermediate field of $L\subseteq\operatorname{LaurentSeries} L$ equal to [`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103) of the $q$-expansion function field of $\Gamma_1(Mp)$, that is, the field generated over $L$ by the coefficientwise image of that field of Laurent series. Let $A$ be a discrete valuation domain with an algebra structure on $L$ making $L$ its fraction field, with $p$ in the maximal ideal and $\zeta$ in the image of $A$, acting on $K$ compatibly, and let $j\in K$ be nonzero with Laurent expansion the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157). Fix a prime $\ell$ and, with the same data, the field $K_\ell=$ `laurentBaseChange` of the $q$-expansion function field of $\Gamma_1(Mp)\cap\Gamma_0(Mp\ell)$, an $A$-algebra compatibly with $L$, together with a nonzero $j_\ell\in K_\ell$ having the same $q$-expansion. Assume given a morphism $\pi_\alpha$ over $\operatorname{Spec}A$ from the two-chart model of $(A,K_\ell,j_\ell)$ to that of $(A,K,j)$ (the model glued from the spectra of the subalgebras of elements integral over $A[j]$, resp. over $A[j^{-1}]$), with $\pi_\alpha$ finite and surjective on points, together with an $A$-algebra map $\iota_\alpha$ from the finite chart $\{x\in K: x$ integral over $A[j]\}$ to the corresponding finite chart of $(A,K_\ell,j_\ell)$ that preserves Laurent expansions, and the compatibility `ιFin` followed by $\pi_\alpha$ equals $\operatorname{Spec}(\iota_\alpha)$ followed by `ιFin`. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and let $c:C\to\operatorname{Spec}k$ be proper, smooth of relative dimension one and geometrically integral, with $C$ integral, equipped with a closed immersion $i$ over $\operatorname{Spec}k$ into the special fibre $X_k$, the pullback of the two-chart model of $(A,K,j)$ along $\operatorname{Spec}k\to\operatorname{Spec}A$; assume that every point of $X_k$ specialising to the image of the generic point of $C$ equals that image. Finally let $\pi_{\alpha,k}$ be a morphism between the two special fibres commuting with both projections of the two pullback squares. Then, provided $\ell\neq p$, the fibre product of $\pi_{\alpha,k}$ and $i$ over $X_k$ is a reduced scheme.
--
--   This is the statement that, away from the residue characteristic, the preimage under the first Hecke degeneracy map $\pi_\alpha$ of an irreducible component of the mod-$p$ fibre of the $X_1(Mp)$ model is reduced, the geometric input being the finite étale nature of the $\Gamma_0(\ell)$-structure for $\ell\neq p$ together with reducedness of the special fibre at the cusps. It feeds the construction of a section of the base-changed degeneracy map over such a component, used in the analysis of the Hecke correspondence on special fibres underlying level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_isReduced_pullback_heckeDegeneracy_baseChange_specialFibre_component_of_ne_of_specializes_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.isReduced_pullback_heckeDegeneracy_baseChange_specialFibre_component_of_ne_of_specializes_twoChartModel_x1_mul
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

    (πα : SchemeHomOver (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (ModularCurve.TwoChart.modelTo A (↥K) j))
    [IsFinite πα.1] (hsurjα : Function.Surjective πα.1.base)
    (ια : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ))
    (hια : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ια b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ((b : ↥K) : LaurentSeries L))
    (hπα : ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πα.1 = Spec.map (CommRingCat.ofHom ια.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C : Scheme.{0}) (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (i : SchemeHomOver c (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) [IsClosedImmersion i.1]

    [IsIntegral C]
    (hη : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)),
      z ⤳ i.1.base (genericPoint C) → z = i.1.base (genericPoint C))

    (παk : pullback (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (hπαk₁ : παk ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k) ≫ πα.1)
    (hπαk₂ : παk ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k)) :
    ℓ ≠ p → IsReduced (pullback παk i.1) := by sorry
