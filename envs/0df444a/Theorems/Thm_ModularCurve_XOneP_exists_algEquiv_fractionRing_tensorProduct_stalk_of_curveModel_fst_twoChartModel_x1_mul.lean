-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_fractionRing_tensorProduct_stalk_of_curveModel_fst_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_algEquiv_fractionRing_tensorProduct_stalk_of_curveModel_fst_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/5e59d194-dccb-5112-8c70-1a5802b8b6ef
-- title:
--   Function field of a special-fibre component as a fraction field of k⊗_Amathcal O_{X,z}
-- statement:
--   Fix a prime $p$, an integer $M\ge 5$ with $p\nmid M$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb Q$ of order $p$, and a primitive $p$-th root of unity $\zeta\in L$. Let $K$ be the intermediate field of $L\subseteq L((q))$ obtained by adjoining to $L$ the coefficientwise image under $\mathbb Q\to L$ of the function field $x_1$ of level $Mp$ inside $\mathbb Q((q))$, let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly with $A\to L\to K$, and let $j\in K$ be a nonzero element whose image in $L((q))$ is the coefficientwise image of the $q$-expansion $\mathrm{jq}$. Write $X$ for the two-chart model over $A$ attached to $(K,j)$, the pushout of its two affine charts, with structure morphism $X\to\operatorname{Spec}A$, and let $k$ be an algebraically closed field of characteristic $p$ which is an $A$-algebra, so that $X_k=X\times_{\operatorname{Spec}A}\operatorname{Spec}k$ is defined. Assume given two schemes $C_1,C_2$ proper, smooth of relative dimension $1$ and geometrically integral over $\operatorname{Spec}k$, closed immersions $i_1,i_2$ of $C_1,C_2$ into $X_k$ over $\operatorname{Spec}k$ whose images together cover every point of $X_k$, with $C_1\times_{X_k}C_2$ reduced and of finite cardinality $n>0$; further a section $\varepsilon$ of $X\to\operatorname{Spec}A$, sections $\varepsilon_1,\varepsilon_2$ of $C_1,C_2$ over $\operatorname{Spec}k$ with $\varepsilon_1$ followed by $i_1$ equal to the base change of $\varepsilon$ to $k$, and an integral weight-one form $w$ of level $M$ over $k$ (a modular form of weight $1$ on $\Gamma_1(M)$ with an integral $q$-expansion whose reduction coefficient over $k$ is nonzero). The conclusion: for every field $F$ that is a $k$-algebra, every curve model $\mathrm{Mdl}$ of $F$ over $k$ (an integral proper smooth relative-dimension-one scheme over $\operatorname{Spec}k$ together with an identification of $F$ with its function field, a bijection between closed points and places, the corresponding identification of stalks with valuation subrings, and the property that finite sets of points lie in an affine open) and every isomorphism $e$ of $\mathrm{Mdl}.C$ with $C_1$ compatible with the morphisms to $\operatorname{Spec}k$, and for every generic point $\xi$ of $C_1$, the stalk $\mathcal O_{X,z}$ of $X$ at the image $z$ of $\xi$ under $i_1$ followed by the first projection $X_k\to X$, regarded as an $A$-algebra via the germ at $z$ of the structure morphism, admits a minimal prime $\mathfrak q$ of $k\otimes_A\mathcal O_{X,z}$ for which there is a $k$-algebra isomorphism $F\cong\operatorname{Frac}\big((k\otimes_A\mathcal O_{X,z})/\mathfrak q\big)$.
--
--   This identifies the function field of the first of the two components of the geometric special fibre of the two-chart model with the fraction field of a minimal-prime quotient of the base change $k\otimes_A\mathcal O_{X,z}$ of the local ring at the corresponding point of $X$; the hypotheses describing the modular situation are those of the surrounding analysis of the special fibre of $X_1(Mp)$ at $p$. It is cited in the passage from this description to the valuation-subring formulation used in the study of the components.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_algEquiv_fractionRing_tensorProduct_stalk_of_curveModel_fst_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
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

theorem ModularCurve.XOneP.exists_algEquiv_fractionRing_tensorProduct_stalk_of_curveModel_fst_twoChartModel_x1_mul
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
    ∀ ξ : ↥C₁, IsGenericPoint ξ ⊤ →
      letI : Algebra A ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ)) :=
        RingHom.toAlgebra (((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ) trivial).hom.comp
          ((((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom).comp
            (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
      ∃ (𝔮 : Ideal (TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ))))
        (_ : 𝔮 ∈ minimalPrimes (TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ)))),
        Nonempty (F ≃ₐ[k] FractionRing (TensorProduct A k ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk ((i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).base ξ)) ⧸ 𝔮)) := by sorry
