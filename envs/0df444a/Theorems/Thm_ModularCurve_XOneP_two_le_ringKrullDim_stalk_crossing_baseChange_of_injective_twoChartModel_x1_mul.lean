-- Prove2me | Theorems.Thm_ModularCurve_XOneP_two_le_ringKrullDim_stalk_crossing_baseChange_of_injective_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.two_le_ringKrullDim_stalk_crossing_baseChange_of_injective_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/04e46206-230e-5a11-bbb9-82689ca7739a
-- title:
--   Stalk at a crossing of the two-chart model has dimension ≥ 2
-- statement:
--   Fix a prime $p$ and $M$ with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of level $\{p\}$, let $\zeta \in L$ be a primitive $p$-th root of unity, and let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the image of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) under the coefficientwise map [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81). Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, with a compatible $A$-algebra structure on $K$, and let $j \in K$ be nonzero with image in $\mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81). Write $X \to \operatorname{Spec} A$ for [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), the morphism obtained from the finite and infinite chart algebras by the pushout description. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$. Assume given two schemes $C_1, C_2$ with proper, smooth of relative dimension one, geometrically integral and integral structure morphisms $c_1, c_2$ to $\operatorname{Spec} k$, together with closed immersions $i_1, i_2$ from $C_1, C_2$ into the fibre product $X \times_{\operatorname{Spec} A} \operatorname{Spec} k$ commuting with the projection to $\operatorname{Spec} k$, such that every point of that fibre product lies in the image of $i_1$ or of $i_2$, the scheme-theoretic intersection $C_1 \times_{X_k} C_2$ is reduced, and its cardinality is $n$ with $0 < n$. Let $O$ be a discrete valuation domain with an injective ring map $\rho_O : A \to O$, a generator $\varpi$ of its maximal ideal, and a ring map $\mathrm{to}\kappa : O \to k$ with $\mathrm{to}\kappa \circ \rho_O$ the structure map $A \to k$. Let $\mathrm{bc} : X \times_A \operatorname{Spec} k \to X \times_A \operatorname{Spec} O$ be a morphism compatible with the first projections and intertwining the second projections via $\operatorname{Spec}$ of $\mathrm{to}\kappa$. Then for every point $\nu$ of $C_1 \times_{X_k} C_2$, the stalk of the structure sheaf of $X \times_A \operatorname{Spec} O$ at the image of $\nu$ under the first projection followed by $i_1$ followed by $\mathrm{bc}$ has Krull dimension at least $2$ (as an element of $\mathrm{WithBot}\,\mathbb{N}_\infty$).
--
--   This is the local dimension estimate at a crossing point of the special fibre of the two-chart integral model of $X_1(Mp)$: the image of an intersection point of the two components in the base change to a coefficient discrete valuation ring $O$ is a point whose local ring has dimension at least two, the injectivity of $A \to O$ guaranteeing that the point lies over the closed point of $\operatorname{Spec} O$. It is the dimension hypothesis used in the construction of an oriented étale crossing chart of the form $O[u,v]/(uv - \varpi^e)$, and is cited by [`ModularCurve.XOneP.forall_exists_orientedEtaleCrossingChart_baseChange_of_injective_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.forall_exists_orientedEtaleCrossingChart_baseChange_of_injective_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_two_le_ringKrullDim_stalk_crossing_baseChange_of_injective_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_ModularCurve_DRModelPackageCrossingFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.two_le_ringKrullDim_stalk_crossing_baseChange_of_injective_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ρO : A →+* O) (hρO : Function.Injective ρO) (ϖ : O) (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ})
    (toκ : O →+* k) (htoκ : toκ.comp ρO = algebraMap A k)

    (bc : pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO)))
    (hbc₁ : bc ≫ pullback.fst _ _ = pullback.fst _ _)
    (hbc₂ : bc ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom toκ))
    [IsIntegral C₁] [IsIntegral C₂] (ν : ↥(pullback i₁.1 i₂.1)) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim ((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (Spec.map (CommRingCat.ofHom ρO))).presheaf.stalk ((pullback.fst i₁.1 i₂.1 ≫ i₁.1 ≫ bc).base ν)) := by sorry
