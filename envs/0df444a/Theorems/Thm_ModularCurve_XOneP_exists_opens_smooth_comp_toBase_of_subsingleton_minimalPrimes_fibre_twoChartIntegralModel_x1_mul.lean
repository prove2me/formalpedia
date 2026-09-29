-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_opens_smooth_comp_toBase_of_subsingleton_minimalPrimes_fibre_twoChartIntegralModel_x1_mul
-- name    : ModularCurve.XOneP.exists_opens_smooth_comp_toBase_of_subsingleton_minimalPrimes_fibre_twoChartIntegralModel_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/9cda63c2-e8dc-58f7-bdf7-64ac6ad1d870
-- title:
--   Smoothness over the base at one-branch points of the special fibre
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $5 \le M$ and $p \nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $p$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subseteq L((q))$ obtained by adjoining to $L$ the coefficientwise image, under $\mathbb{Q} \to L$, of the $q$-expansion field [`ModularCurve.x1FunctionField (M * p)`](def/ModularCurve_X1.html#L137) (the field attached to $\Gamma_1(Mp)$ inside $\mathbb{Q}((q))$). Let $A$ be a discrete valuation domain with fraction field $L$, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A \to L$, with $K$ an $A$-algebra compatibly with $A \to L \to K$. Let $j \in K$ be nonzero with image in $L((q))$ the coefficientwise image of the $q$-expansion $\mathrm{jq} = q^{-1}\cdot(\text{power series } \mathrm{jNumQ})$, and let $\varpi$ generate the maximal ideal of $A$. Write $X =$ [`AlgebraicCurve.TwoChartIntegralModel A K j`](def/AlgebraicCurve_TwoChartIntegralModel.html#L236), the scheme obtained by gluing $\operatorname{Spec}$ of the $A$-subalgebras of $K$ attached to $j$ and to $j^{-1}$ along their common middle chart, with structure morphism `toBase` to $\operatorname{Spec} A$. Let $z \in X$ and let $\varpi_z$ be the germ at $z$ of the global section pulled back from $\varpi$, assumed to lie in the maximal ideal of the stalk $\mathcal{O}_{X,z}$ and such that the ideal $(\varpi_z)$ of $\mathcal{O}_{X,z}$ has at most one minimal prime. Then there is an open subscheme $U \subseteq X$ containing $z$ such that the inclusion $U \hookrightarrow X$ followed by `toBase` is smooth.
--
--   This is the assertion that the two-chart integral model of the modular curve for $\Gamma_1(Mp)$ over the discrete valuation ring $A \subset \mathbb{Q}(\zeta_p)$ above $p$ is smooth over $A$ in a neighbourhood of each point of the special fibre through which only one branch passes — the ordinary points and the cusps, as opposed to the supersingular crossings. It feeds the construction of the stable model and its regularity and degeneration properties, and the local computations of the maximal ideals of the localised charts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_opens_smooth_comp_toBase_of_subsingleton_minimalPrimes_fibre_twoChartIntegralModel_x1_mul.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem ModularCurve.XOneP.exists_opens_smooth_comp_toBase_of_subsingleton_minimalPrimes_fibre_twoChartIntegralModel_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (z : ↥(AlgebraicCurve.TwoChartIntegralModel A (↥K) j))
    (ϖz : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)
    (hϖz : ϖz = ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.germ ⊤ z trivial).hom
      (((AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ϖ)))
    (hz : ϖz ∈ IsLocalRing.maximalIdeal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z))
    (hone : (Ideal.span {ϖz} :
      Ideal ((AlgebraicCurve.TwoChartIntegralModel A (↥K) j).presheaf.stalk z)).minimalPrimes.Subsingleton) :
    ∃ U : (AlgebraicCurve.TwoChartIntegralModel A (↥K) j).Opens,
      z ∈ U ∧ Smooth (U.ι ≫ AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j) := by sorry
