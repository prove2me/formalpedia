-- Prove2me | Theorems.Thm_ModularCurve_XOneP_valuationSubring_eq_gauss_of_ringEquiv_stalk_germ_eq_of_section_eq_comp_iotaInf_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.valuationSubring_eq_gauss_of_ringEquiv_stalk_germ_eq_of_section_eq_comp_iotaInf_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/ae7182e6-ce83-534d-85b0-da5d965df8c0
-- title:
--   Component meeting the cusp ∞ has Gauss valuation ring
-- statement:
--   Fix a prime $p$ and $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero that is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$, and a primitive $p$-th root of unity $\zeta\in L$. Let $K$ be the intermediate field of $L\subseteq L((q))$ obtained by adjoining to $L$ the coefficientwise image of the function field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) of $X_1(Mp)$ inside $\mathbb{Q}((q))$, let $A$ be a discrete valuation ring with fraction field $L$ such that $p$ lies in $\mathfrak m_A$ and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly with $L$, and let $j\in K$, $j\neq 0$, have Laurent expansion the coefficientwise image of $q^{-1}\cdot jNumQ$. Let $k$ be an algebraically closed field of characteristic $p$ over $A$, and let $c_1:C_1\to\operatorname{Spec}k$, $c_2:C_2\to\operatorname{Spec}k$ be proper, smooth of relative dimension $1$ and geometrically integral, with closed immersions $i_1,i_2$ over $\operatorname{Spec}k$ into the base change to $k$ of the structure morphism [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) of the two-chart model, whose topological images together cover that base change. Let $\varepsilon$ be a section of `modelTo` over $\operatorname{Spec}A$ and $\varepsilon_1$ a section of $c_1$ with $\varepsilon_1$ followed by $i_1$ equal to the base-changed section `sectionBaseChange k ε`. Let $\psi$ be a ring homomorphism from the infinity chart algebra (the elements of $K$ integral over $A[j^{-1}]$) to $A$ which retracts $A$ and sends $f$ to the $q^0$-coefficient of its Laurent expansion, and assume $\varepsilon$ is $\operatorname{Spec}\psi$ followed by the infinity-chart inclusion `ιInf`, and that no point of $\operatorname{Spec}A$ is carried by $\varepsilon$ into the image of the finite-chart inclusion `ιFin`. Let $W_0$ be the valuation subring of $K$ consisting of those $f$ for which there are power series $x,y$ over $A$ with $y$ nonzero modulo $\mathfrak m_A$ and $f\cdot y(q)=x(q)$ in $L((q))$ (the Gauss ring). Let $\xi_1$ be a generic point of $C_1$ whose image under $i_1$ followed by the first projection lies in the open finite chart, and let $V_1$ be a valuation subring of $K$ containing the image of $A$, with $\mathfrak m_A$ mapping into its nonunits, and such that for every polynomial $P$ over $A$ with nonzero reduction modulo $\mathfrak m_A$ both $P(j)$ and $P(j)^{-1}$ lie in $V_1$; assume finally a ring isomorphism $\varphi_1$ from the stalk of [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236) at that image point onto $V_1$ which sends the germ of the section attached to $a$ in the finite chart algebra to $a$, for every such $a$. Then $V_1=W_0$.
--
--   This identifies, for the two-chart integral model of $X_1(Mp)$ over the ring of integers of $\mathbb{Q}(\zeta_p)$ localised at $p$, the component of the geometric special fibre met by the reduction of the cusp $\infty$: its local ring at the generic point is exactly the Gauss valuation ring of $K$, the branch on which the $q$-expansion at $\infty$ reduces. It is used in the construction of an isomorphism between a component of the special fibre and the Igusa curve attached to $X_1(M)$ in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_valuationSubring_eq_gauss_of_ringEquiv_stalk_germ_eq_of_section_eq_comp_iotaInf_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.valuationSubring_eq_gauss_of_ringEquiv_stalk_germ_eq_of_section_eq_comp_iotaInf_twoChartModel_x1_mul
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

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (ψ : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →+* A)
    (hψA : ∀ a : A, ψ (algebraMap A ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) a) = a)
    (hψ0 : ∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
      algebraMap A L (ψ f) = (((f : ↥K) : LaurentSeries L)).coeff 0)
    (hε : ε.1 = Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιInf A (↥K) j)
    (hεFin : ∀ y : ↥(Spec (CommRingCat.of A)), ε.1.base y ∉ Set.range (ModularCurve.TwoChart.ιFin A (↥K) j).base)

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))

    (ξ₁ : ↥C₁) (hξ₁ : IsGenericPoint ξ₁ ⊤)
    (hz₁ : (i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₁ ∈ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
    (V₁ : ValuationSubring ↥K)
    (hVA : ∀ a : A, algebraMap A ↥K a ∈ V₁)
    (hVm : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V₁.nonunits)
    (hVj : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
      Polynomial.aeval j P ∈ V₁ ∧ (Polynomial.aeval j P)⁻¹ ∈ V₁)
    (φ₁ : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₁) ≃+* ↥V₁)
    (hφ₁ : ∀ a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
      ((φ₁ (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤) ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ₁) hz₁).hom (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))) : ↥V₁) : ↥K) = (a : ↥K)) :
    V₁ = W₀ := by sorry
