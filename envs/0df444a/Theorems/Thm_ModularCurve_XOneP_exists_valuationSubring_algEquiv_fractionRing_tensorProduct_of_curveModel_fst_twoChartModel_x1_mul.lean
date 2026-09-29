-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_valuationSubring_algEquiv_fractionRing_tensorProduct_of_curveModel_fst_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_valuationSubring_algEquiv_fractionRing_tensorProduct_of_curveModel_fst_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/505dd979-62ad-524f-9fcd-e2c0c47c76e0
-- title:
--   Component function fields of X₁(Mp)_k from valuation subrings
-- statement:
--   Fix a prime $p$ and $M\ge 5$ with $p\nmid M$, a characteristic-zero field $L$ that is a $\{p\}$-cyclotomic extension of $\mathbb Q$, a primitive $p$-th root of unity $\zeta\in L$, and the intermediate field $K$ of $L\subseteq L((q))$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield generated over $L$ by the coefficientwise image in $L((q))$ of the function field of $X_1(Mp)$ over $\mathbb Q$. Let $A$ be a discrete valuation ring with fraction field $L$ such that $p\in\mathfrak m_A$ and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly with $L$, and let $j\in K$ be the element whose Laurent expansion is [`ModularCurve.coeffEmb L ModularCurve.jq`](def/ModularCurve_LaurentCoeff.html#L81), assumed nonzero. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$. Let $c_1:C_1\to\operatorname{Spec}k$ and $c_2:C_2\to\operatorname{Spec}k$ be proper, smooth of relative dimension $1$ and geometrically integral, and let $i_1,i_2$ be closed immersions of $C_1,C_2$ into the base change to $k$ of the two-chart model [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252), compatible with the structure morphisms to $\operatorname{Spec}k$; assume their images jointly cover every point of that base change, that the fibre product $C_1\times C_2$ over it is reduced, and that its underlying set has cardinality $n>0$. Assume given a section $\varepsilon$ of [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) over $\operatorname{Spec}A$, sections $\varepsilon_1,\varepsilon_2$ of $c_1,c_2$ over $\operatorname{Spec}k$ with $\varepsilon_1$ followed by $i_1$ equal to the base-changed section `sectionBaseChange k ε`, and an object `w : ModularCurve.IntegralWeightOneForm k M`, namely a weight-one modular form on $\Gamma_1(M)$ together with an integral power series that is its $q$-expansion and whose specialisation `intSeriesC k` is nonzero. Then for every field $F$ that is a $k$-algebra, every [`AlgebraicCurve.CurveModel k F`](def/AlgebraicCurve_CurveModel.html#L23) (an integral scheme, proper and smooth of relative dimension $1$ over $k$, with a ring isomorphism of $F$ with its function field extending $k$, a bijection between its closed points and the places of $F/k$ matching stalk images with valuation subrings, and every finite set of points contained in an affine open) and every isomorphism $e$ of its underlying scheme with $C_1$ over $\operatorname{Spec}k$, there exist a valuation subring $V$ of $K$ such that $A$ maps into $V$, every element of $\mathfrak m_A$ maps into the nonunits of $V$, and for every polynomial $P$ over $A$ with nonzero reduction modulo $\mathfrak m_A$ both $P(j)$ and $P(j)^{-1}$ lie in $V$; an $A$-algebra structure on $V$ whose structure map agrees with $A\to K$; and a minimal prime $\mathfrak q$ of $k\otimes_A V$ such that $F$ is isomorphic as a $k$-algebra to $\operatorname{Frac}\big((k\otimes_A V)/\mathfrak q\big)$.
--
--   This is the components-to-branches dictionary for the reduction of $X_1(Mp)$ at $p$: the function field of a component of the geometric special fibre of the two-chart model is recovered as the fraction field of $k\otimes_A V$ modulo a minimal prime, for a valuation subring $V$ of $K$ lying over $\mathfrak m_A$ and over the generic point of the $j$-line in characteristic $p$. It feeds the identification of that function field with an Igusa-type function field over $k$, used in the comparison of the two components of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_valuationSubring_algEquiv_fractionRing_tensorProduct_of_curveModel_fst_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicGeometry.SmoothProperCurve

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open scoped TensorProduct

theorem ModularCurve.XOneP.exists_valuationSubring_algEquiv_fractionRing_tensorProduct_of_curveModel_fst_twoChartModel_x1_mul
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

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)
    (w : ModularCurve.IntegralWeightOneForm k M) :
    ∀ (F : Type) [Field F] [Algebra k F] (Mdl : AlgebraicCurve.CurveModel k F) (e : Mdl.C ≅ C₁),
      e.hom ≫ c₁ = Mdl.toBase →
      ∃ (V : ValuationSubring ↥K)
        (_ : ∀ a : A, algebraMap A ↥K a ∈ V)
        (_ : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A ↥K a ∈ V.nonunits)
        (_ : ∀ P : Polynomial A, P.map (IsLocalRing.residue A) ≠ 0 →
          Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)
        (algV : Algebra A ↥V) (_ : ∀ a : A, ((algebraMap A ↥V a : ↥V) : ↥K) = algebraMap A ↥K a)
        (𝔮 : Ideal (TensorProduct A k ↥V)) (_ : 𝔮 ∈ minimalPrimes (TensorProduct A k ↥V)),
        Nonempty (F ≃ₐ[k] FractionRing (TensorProduct A k ↥V ⧸ 𝔮)) := by sorry
