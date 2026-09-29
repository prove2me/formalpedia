-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_iso_comp_eq_specialFibre_components_of_apply_eq_diamondAut_of_coprime_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_iso_comp_eq_specialFibre_components_of_apply_eq_diamondAut_of_coprime_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/cff9d6b6-20aa-5d08-9eda-c04a0566cb47
-- title:
--   Diamond model automorphism preserves both special-fibre components
-- statement:
--   Fix a prime $p$ and $M\ge 5$ with $p\nmid M$, a characteristic-zero field $L$ that is a $p$-th cyclotomic extension of $\mathbb{Q}$, a primitive $p$-th root of unity $\zeta\in L$, and an intermediate field $K$ of $L\subseteq \mathrm{LaurentSeries}\,L$ equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), i.e. the field generated over $L$ by the coefficientwise image of the function field of $X_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, with $K$ an $A$-algebra compatibly, and let $j\in K$ be a nonzero element whose Laurent series is the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157) pushed to $L$. Write $X$ for the two-chart model [`ModularCurve.TwoChartModel A K j`](def/ModularCurve_TwoChartModel.html#L229) (the pushout of the two charts) with structure morphism [`ModularCurve.TwoChart.modelTo A K j`](def/ModularCurve_TwoChartModel.html#L252) to $\mathrm{Spec}\,A$. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, and let $c_1\colon C_1\to \mathrm{Spec}\,k$, $c_2\colon C_2\to \mathrm{Spec}\,k$ be proper, smooth of relative dimension $1$ and geometrically integral, together with closed immersions $i_1,i_2$ of $C_1,C_2$ into the special fibre $X\times_{\mathrm{Spec}\,A}\mathrm{Spec}\,k$ commuting with the structure morphisms, such that every point of the special fibre lies in the image of $i_1$ or of $i_2$, the scheme-theoretic intersection $C_1\times_{X_s}C_2$ is reduced, and its number of points equals some $n>0$. Assume further given a section $\varepsilon$ of `modelTo` over $\mathrm{Spec}\,A$, sections $\varepsilon_1,\varepsilon_2$ of $c_1,c_2$ with $\varepsilon_1$ followed by $i_1$ equal to the base change of $\varepsilon$, a natural number $d$ coprime to $Mp$, and an $L$-algebra automorphism $\theta$ of $K$ which agrees, on elements with equal Laurent series, with [`ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d)`](def/ModularCurve_X1Diamond.html#L24). Finally let $w$ be an automorphism of $X$ over $\mathrm{Spec}\,A$ and $\rho$ a ring endomorphism of the finite chart algebra [`ModularCurve.TwoChart.chartAlgFin A K j`](def/ModularCurve_TwoChartModel.html#L135) (the elements of $K$ integral over $A[j]$) which induces $\theta$ on elements, with $\mathrm{Spec}(\rho)$ followed by the chart immersion `ιFin` equal to `ιFin` followed by $w$. The conclusion is that there exist isomorphisms $\alpha_1\colon C_1\cong C_1$ and $\alpha_2\colon C_2\cong C_2$ over $k$ (that is, $\alpha_\ell$ followed by $c_\ell$ equals $c_\ell$) with $\alpha_\ell$ followed by $i_\ell$ equal to $i_\ell$ followed by `curveChange w.hom hw (specMap A k)`, the special fibre of $w$.
--
--   This is the component half of the special-fibre description of the diamond operators on $X_1(Mp)$ in characteristic $p$: the automorphism of the integral two-chart model attached to $\langle d\rangle$ for any $d$ prime to $Mp$ fixes each of the two irreducible components of the special fibre, hence restricts to an automorphism of each of the two smooth proper curves covering it. It is used in the descent of the diamond operators to the components, where the induced automorphisms of $C_1$ and $C_2$ and their effect on Jacobians are compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_iso_comp_eq_specialFibre_components_of_apply_eq_diamondAut_of_coprime_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra AlgebraicGeometry.SmoothProperCurve

theorem ModularCurve.XOneP.exists_iso_comp_eq_specialFibre_components_of_apply_eq_diamondAut_of_coprime_twoChartModel_x1_mul
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
    (d : ℕ) (hd : d.Coprime (M * p))
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (y : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (y : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) y :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))

    (w : ModularCurve.TwoChartModel A (↥K) j ≅ ModularCurve.TwoChartModel A (↥K) j)
    (hw : w.hom ≫ ModularCurve.TwoChart.modelTo A (↥K) j = ModularCurve.TwoChart.modelTo A (↥K) j)
    (ρ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))
    (hρ : ∀ x, ((ρ x : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) = θ x)
    (hsq : Spec.map (CommRingCat.ofHom ρ) ≫ ModularCurve.TwoChart.ιFin A (↥K) j = ModularCurve.TwoChart.ιFin A (↥K) j ≫ w.hom) :
    (∃ α₁ : C₁ ≅ C₁, α₁.hom ≫ c₁ = c₁ ∧
      α₁.hom ≫ i₁.1 = i₁.1 ≫ curveChange w.hom hw (specMap A k)) ∧
    (∃ α₂ : C₂ ≅ C₂, α₂.hom ≫ c₂ = c₂ ∧
      α₂.hom ≫ i₂.1 = i₂.1 ≫ curveChange w.hom hw (specMap A k)) := by sorry
