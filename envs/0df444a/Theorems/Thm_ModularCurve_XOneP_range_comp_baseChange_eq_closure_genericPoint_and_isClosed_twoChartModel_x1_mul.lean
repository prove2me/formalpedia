-- Prove2me | Theorems.Thm_ModularCurve_XOneP_range_comp_baseChange_eq_closure_genericPoint_and_isClosed_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.range_comp_baseChange_eq_closure_genericPoint_and_isClosed_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/d502aafb-0013-51d7-bf05-e7535ebebade
-- title:
--   Images of the two components in X_O are closed
-- statement:
--   Fix a prime $p$ and an integer $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero that is a $p$-th cyclotomic extension of $\mathbb{Q}$, and a primitive $p$-th root of unity $\zeta\in L$. Let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained as [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield generated over $L$ by the image under [`ModularCurve.coeffEmb L`](def/ModularCurve_LaurentCoeff.html#L81) of the function field `x1FunctionField (M * p)` of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly with $A\to L\to K$, and let $j\in K$ be a nonzero element whose image in $\mathrm{LaurentSeries}\,L$ is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81). Write $X=$ [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) for the two-chart model over $\operatorname{Spec} A$, glued from the finite and infinite chart algebras. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and let $X_k$ denote the pullback of $X$ along $\operatorname{Spec} k\to\operatorname{Spec} A$. Let $C_1,C_2$ be schemes with structure morphisms $c_1,c_2$ to $\operatorname{Spec} k$ that are proper, smooth of relative dimension $1$, geometrically integral and integral, and let $i_1,i_2$ be morphisms over $\operatorname{Spec} k$ from $C_1,C_2$ to $X_k$ (each commuting with the second projection of the pullback) whose underlying scheme morphisms are closed immersions, such that every point of $X_k$ lies in the range of $i_1$ or of $i_2$, the scheme-theoretic intersection $C_1\times_{X_k}C_2$ is reduced, and its underlying set has cardinality $n>0$. Let $O$ be a discrete valuation domain with an injective ring homomorphism $\rho_O\colon A\to O$, a uniformiser $\varpi$ generating the maximal ideal, and a ring homomorphism $O\to k$ whose composite with $\rho_O$ is $A\to k$; let $\mathrm{bc}\colon X_k\to X_O$ be a morphism into the pullback of $X$ along $\operatorname{Spec} O\to\operatorname{Spec} A$ that commutes with the first projections and is compatible with the second projections via $\operatorname{Spec}$ of $O\to k$. Then for $i=1,2$ the set-theoretic range of the map underlying $i_i$ followed by $\mathrm{bc}$ equals the closure of the single point which is the image of the generic point of $C_i$, and this range is closed in $X_O$.
--
--   This is the $X_1(Mp)$ analogue of the statement that, over a coefficient discrete valuation ring $O$ above $A$, each of the two components covering the geometric special fibre of the model maps onto the closure of an irreducible branch generic point, so that the two branch closures are closed subsets of $X_O$. It feeds the construction of oriented étale crossing charts at the base change and the identification of the ideal sheaves cutting out the two branches over $O$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_range_comp_baseChange_eq_closure_genericPoint_and_isClosed_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.range_comp_baseChange_eq_closure_genericPoint_and_isClosed_twoChartModel_x1_mul
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
    [IsIntegral C₁] [IsIntegral C₂] :
    (Set.range (i₁.1 ≫ bc).base = closure {(i₁.1 ≫ bc).base (genericPoint C₁)} ∧ IsClosed (Set.range (i₁.1 ≫ bc).base)) ∧
    (Set.range (i₂.1 ≫ bc).base = closure {(i₂.1 ≫ bc).base (genericPoint C₂)} ∧ IsClosed (Set.range (i₂.1 ≫ bc).base)) := by sorry
