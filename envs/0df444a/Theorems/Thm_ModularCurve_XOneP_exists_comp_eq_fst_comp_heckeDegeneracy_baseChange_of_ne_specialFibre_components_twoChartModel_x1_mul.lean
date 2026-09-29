-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_comp_eq_fst_comp_heckeDegeneracy_baseChange_of_ne_specialFibre_components_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.exists_comp_eq_fst_comp_heckeDegeneracy_baseChange_of_ne_specialFibre_components_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/aa241c21-5651-587d-9472-79cebe60e711
-- title:
--   Hecke degeneracies preserve special-fibre components for ℓ ≠ p
-- statement:
--   Fix a prime $p$, an integer $M \ge 5$ with $p \nmid M$, a field $L$ of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $p$, and a primitive $p$-th root of unity $\zeta \in L$. Let $K$ be the intermediate field of $L \subseteq \mathrm{LaurentSeries}\,L$ generated over $L$ by the coefficientwise image of the $q$-expansion function field `x1FunctionField (M * p)` of level $\Gamma_1(Mp)$, and let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ lies in the image of $A$, together with an $A$-algebra structure on $K$ compatible via the tower $A \to L \to K$. Let $j \in K$ be a nonzero element whose Laurent series is the image of `jq` under `coeffEmb L`, and let $X =$ `TwoChart.modelTo A K j` $\to \operatorname{Spec} A$ be the associated two-chart model. Let $\ell$ be a prime and let $K_\ell$ be the corresponding $L$-generated subfield attached to `x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)` (level $\Gamma_1(Mp) \cap \Gamma_0(Mp\ell)$), an $A$-algebra in the same way, with a nonzero $j_\ell \in K_\ell$ having the same $q$-expansion `jq`, and $X_\ell$ its two-chart model. Assume `HeckeBetaOneDefined (M * p) ℓ`, i.e. that $y \mapsto$ `qExpand ℚ ℓ` $y$ carries the level-$\Gamma_1(Mp)$ function field into the level-$(\Gamma_1(Mp),\Gamma_0(Mp\ell))$ one. Let $\pi_\alpha, \pi_\beta : X_\ell \to X$ be morphisms over $\operatorname{Spec} A$ that are finite and surjective on points, and let $\iota_\alpha, \iota_\beta$ be $A$-algebra maps from the finite-chart algebra `TwoChart.chartAlgFin A K j` to `TwoChart.chartAlgFin A K_ℓ jℓ` acting on Laurent series as the identity, respectively as `qExpand L ℓ`, and inducing $\pi_\alpha$, $\pi_\beta$ on the finite charts in the sense that `TwoChart.ιFin` of $X_\ell$ followed by $\pi_\alpha$ (resp. $\pi_\beta$) equals $\operatorname{Spec}(\iota_\alpha)$ (resp. $\operatorname{Spec}(\iota_\beta)$) followed by `TwoChart.ιFin` of $X$. Let $k$ be an algebraically closed $A$-algebra field of characteristic $p$, let $X_k$ and $(X_\ell)_k$ denote the pullbacks of the two models along $\operatorname{Spec} k \to \operatorname{Spec} A$, and let $c_1 : C_1 \to \operatorname{Spec} k$, $c_2 : C_2 \to \operatorname{Spec} k$ be proper, smooth of relative dimension $1$ and geometrically integral, with closed immersions $i_1 : C_1 \to X_k$, $i_2 : C_2 \to X_k$ over $\operatorname{Spec} k$ whose images cover all points of $X_k$. Finally let $\pi_{\alpha,k}, \pi_{\beta,k} : (X_\ell)_k \to X_k$ be morphisms compatible with the two projections, i.e. their composites with the first projection are the first projection followed by $\pi_\alpha$, resp. $\pi_\beta$, and their composites with the projection to $\operatorname{Spec} k$ are the given one. The conclusion is that if $\ell \neq p$, then for $a = 1, 2$ there is a morphism $e_a : (X_\ell)_k \times_{X_k} C_a \to C_a$ (the fibre product taken along $\pi_{\alpha,k}$ and $i_a$) with $e_a$ followed by $i_a$ equal to the first projection followed by $\pi_{\beta,k}$.
--
--   This is the type-preservation statement for the Hecke correspondence in residue characteristic $p$: scheme-theoretically, $\pi_\beta(\pi_\alpha^{-1}(C_a)) \subseteq C_a$ for each of the two curves covering the special fibre of the two-chart model of $X_1(Mp)$ over the discrete valuation ring $A$, provided $\ell \neq p$. It is the geometric input for the descent of the Hecke operator $T_\ell$ to the components of the special fibre, used by [`ModularCurve.XOneP.exists_descent_heckeGenOne_of_ne_specialFibre_components_of_abelJacobi_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.exists_descent_heckeGenOne_of_ne_specialFibre_components_of_abelJacobi_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_comp_eq_fst_comp_heckeDegeneracy_baseChange_of_ne_specialFibre_components_twoChartModel_x1_mul.lean

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

theorem ModularCurve.XOneP.exists_comp_eq_fst_comp_heckeDegeneracy_baseChange_of_ne_specialFibre_components_twoChartModel_x1_mul
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

        (hβ : ModularCurve.HeckeBetaOneDefined (M * p) ℓ)

    (πα πβ : SchemeHomOver (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (ModularCurve.TwoChart.modelTo A (↥K) j))
    [IsFinite πα.1] [IsFinite πβ.1]
    (hsurjα : Function.Surjective πα.1.base) (hsurjβ : Function.Surjective πβ.1.base)
    (ια ιβ : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) →ₐ[A] ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ))
    (hια : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ια b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) = ((b : ↥K) : LaurentSeries L))
    (hιβ : ∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j), (((ιβ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ)) : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) : LaurentSeries L) =
      ModularCurve.qExpand L ℓ ((b : ↥K) : LaurentSeries L))
    (hπα : ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πα.1 = Spec.map (CommRingCat.ofHom ια.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)
    (hπβ : ModularCurve.TwoChart.ιFin A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ ≫ πβ.1 = Spec.map (CommRingCat.ofHom ιβ.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j)

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)

    (παk πβk : pullback (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))
    (hπαk₁ : παk ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k) ≫ πα.1)
    (hπαk₂ : παk ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k))
    (hπβk₁ : πβk ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.fst (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k) ≫ πβ.1)
    (hπβk₂ : πβk ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = pullback.snd (ModularCurve.TwoChart.modelTo A (↥(ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ (M * p) (M * p * ℓ)))) jℓ) (specMap A k)) :
    ℓ ≠ p →
      (∃ e₁ : pullback παk i₁.1 ⟶ C₁, e₁ ≫ i₁.1 = pullback.fst παk i₁.1 ≫ πβk) ∧
      (∃ e₂ : pullback παk i₂.1 ⟶ C₂, e₂ ≫ i₂.1 = pullback.fst παk i₂.1 ≫ πβk) := by sorry
