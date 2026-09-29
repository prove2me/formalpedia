-- Prove2me | Theorems.Thm_ModularCurve_XOneP_section_comp_eq_spec_comp_section_of_iotaFin_comp_eq_of_coeff_zero_twoChartModel_x1_mul
-- name    : ModularCurve.XOneP.section_comp_eq_spec_comp_section_of_iotaFin_comp_eq_of_coeff_zero_twoChartModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/02e260c0-2dbd-5d24-b359-4241f79f45c5
-- title:
--   Galois invariance of the cusp section of the two-chart model
-- statement:
--   Fix a prime $p$ and $M$ with $5 \le M$ and $p \nmid M$, a characteristic-zero field $L$ that is a $\{p\}$-cyclotomic extension of $\mathbb{Q}$ together with a primitive $p$-th root of unity $\zeta \in L$, and let $K$ be the intermediate field of $L((q))$ obtained by adjoining to $L$ the coefficientwise image under $\mathbb{Q} \to L$ of the $q$-expansion field $\mathtt{qExpFunctionFieldC}\ \mathbb{Q}\ \Gamma_1(Mp)$. Let $A$ be a discrete valuation domain with fraction field $L$ such that $p$ lies in its maximal ideal and $\zeta$ is in the image of $A$, with $K$ an $A$-algebra compatibly with $L$, and let $j \in K$ be nonzero with $q$-expansion the image of $jq = q^{-1}\,\mathtt{jNumQ}$. Write $A_{\mathrm{fin}}$, resp. $A_\infty$, for the $A$-subalgebras of elements of $K$ integral over $A[j]$, resp. $A[j^{-1}]$, and $X = \mathtt{TwoChartModel}$ for the pushout of $\operatorname{Spec} A_{\mathrm{fin}} \leftarrow \operatorname{Spec} A_{\mathrm{mid}} \rightarrow \operatorname{Spec} A_\infty$, with the descended structure morphism $f : X \to \operatorname{Spec} A$, assumed proper, and the chart morphisms $\iota_{\mathrm{fin}}$, $\iota_\infty$. Assume $\mathrm{Gal}(L/\mathbb{Q}) = (L \simeq_{\mathbb{Q}} L)$ acts on $A$ by ring automorphisms compatibly with $A \to L$. Let $\psi : A_\infty \to A$ be a ring homomorphism that is the identity on $A$ and sends $g$ to the element of $A$ whose image in $L$ is the coefficient of $q^0$ of the $q$-expansion of $g$, and let $\varepsilon$ be a section of $f$ (an element of the subtype of morphisms $\operatorname{Spec} A \to X$ over the identity of $\operatorname{Spec} A$) equal to $\operatorname{Spec}(\psi)$ followed by $\iota_\infty$. Then for every $s \in \mathrm{Gal}(L/\mathbb{Q})$, every endomorphism $w_s$ of $X$ with $w_s$ followed by $f$ equal to $f$ followed by $\operatorname{Spec}$ of the action of $s$ on $A$, and every ring automorphism $\rho_s$ of $A_{\mathrm{fin}}$ acting on $q$-expansions coefficientwise by $s$, if $\iota_{\mathrm{fin}}$ followed by $w_s$ equals $\operatorname{Spec}(\rho_s)$ followed by $\iota_{\mathrm{fin}}$, then $\varepsilon$ followed by $w_s$ equals $\operatorname{Spec}$ of the action of $s$ on $A$ followed by $\varepsilon$.
--
--   This is the assertion that the cusp $\infty$, realised as the section of the two-chart integral model of $X_1(Mp)$ over $A$ given by evaluating $q$-expansions at $q = 0$ on the pole chart, is equivariant for every Galois model morphism that is pinned coefficientwise on the finite ($j$-regular) chart. It is used in the construction of the semistable specialisation data with its diamond and inertia operators, where the Galois-invariance of the rigidifying section must be supplied.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_section_comp_eq_spec_comp_section_of_iotaFin_comp_eq_of_coeff_zero_twoChartModel_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem ModularCurve.XOneP.section_comp_eq_spec_comp_section_of_iotaFin_comp_eq_of_coeff_zero_twoChartModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [MulSemiringAction (L ≃ₐ[ℚ] L) A]
    (hΓA : ∀ (s : L ≃ₐ[ℚ] L) (a : A), algebraMap A L (s • a) = s (algebraMap A L a))

    (ψ : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) →+* A)
    (hψA : ∀ a : A, ψ (algebraMap A ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j) a) = a)
    (hψ0 : ∀ f : ↥(ModularCurve.TwoChart.chartAlgInf A (↥K) j),
      algebraMap A L (ψ f) = (((f : ↥K) : LaurentSeries L)).coeff 0)
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hε : ε.1 = Spec.map (CommRingCat.ofHom ψ) ≫ ModularCurve.TwoChart.ιInf A (↥K) j) :
    ∀ (s : L ≃ₐ[ℚ] L) (ws : ModularCurve.TwoChartModel A (↥K) j ⟶ ModularCurve.TwoChartModel A (↥K) j),
      ws ≫ ModularCurve.TwoChart.modelTo A (↥K) j =
        ModularCurve.TwoChart.modelTo A (↥K) j ≫ Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) →
      ∀ (ρs : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j) ≃+* ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)),
      (∀ b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j),
        (((ρs b : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) : ↥K) : LaurentSeries L) =
          ModularCurve.coeffMap (s.toAlgHom.toRingHom) (((b : ↥K)) : LaurentSeries L)) →
      ModularCurve.TwoChart.ιFin A (↥K) j ≫ ws = Spec.map (CommRingCat.ofHom ρs.toRingHom) ≫ ModularCurve.TwoChart.ιFin A (↥K) j →
      ε.1 ≫ ws = Spec.map (CommRingCat.ofHom (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) A s)) ≫ ε.1 := by sorry
