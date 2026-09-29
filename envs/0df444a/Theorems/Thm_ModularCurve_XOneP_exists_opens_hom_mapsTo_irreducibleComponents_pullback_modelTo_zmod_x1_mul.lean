-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_opens_hom_mapsTo_irreducibleComponents_pullback_modelTo_zmod_x1_mul
-- name    : ModularCurve.XOneP.exists_opens_hom_mapsTo_irreducibleComponents_pullback_modelTo_zmod_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/b6fba999-54a4-54af-8f28-f90c95915cf9
-- title:
--   A component-moving self-map on the mod p fibre of X₁(Mp)
-- statement:
--   Let $p$ be a prime and $M \ge 5$ with $p \nmid M$; let $L$ be a field of characteristic zero that is a cyclotomic extension of $\mathbb{Q}$ of order $p$, and $\zeta \in L$ a primitive $p$-th root of unity. Let $K$ be the intermediate field of $L \subseteq L((q))$ obtained as `laurentBaseChange`, i.e. the subfield generated over $L$ by the image, under the coefficientwise map $L((q)) \supseteq$ induced by $\mathbb{Q} \to L$, of the $q$-expansion function field `x1FunctionField (M * p)` of $\Gamma_1(Mp)$ over $\mathbb{Q}$. Let $A$ be a discrete valuation domain with fraction field $L$, with $p$ in its maximal ideal and $\zeta$ in the image of $A$, together with an $A$-algebra structure on $K$ compatible with $A \to L \to K$, and let $j \in K$ be nonzero with $q$-expansion the image of `jq` $= q^{-1}\cdot j_{\mathrm{num}}$ under the coefficientwise embedding. Fix an $A$-algebra structure on $\mathbb{Z}/p$, and let $X$ denote the pullback of the structure morphism `modelTo` of the two-chart model of $K$ over $A$ with respect to $j$ (the pushout of the affine charts attached to `chartAlgFin` and `chartAlgInf`) along $\operatorname{Spec}(\mathbb{Z}/p) \to \operatorname{Spec} A$. Then there exist an open subscheme $U \subseteq X$ and a morphism $\varphi : U \to X$ commuting with the projections to $\operatorname{Spec}(\mathbb{Z}/p)$ (that is, $\varphi$ followed by the second projection equals the open immersion $U \hookrightarrow X$ followed by the second projection) such that: every point $x \in X$ outside $U$ has local ring a domain and a discrete valuation ring, and is a specialisation of some point of $U$; and for every irreducible component $Z$ of $X$ there is an irreducible component $Z' \ne Z$ of $X$ with $\varphi$ mapping the preimage of $Z$ in $U$ into $Z'$.
--
--   This is the chart-level form of the statement that the fibre at $p$ of the two-chart model of $X_1(Mp)$ carries a self-map, coming from the Atkin–Lehner map $j \mapsto j(q^p)$ on the $j$-finite chart, which sends each irreducible component into a different one, the complement of the chart consisting of points with discrete valuation local rings reached by specialisation from the chart. It is used to deduce the corresponding assertion for the two-chart model itself.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_opens_hom_mapsTo_irreducibleComponents_pullback_modelTo_zmod_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.SmoothProperCurve Topology
open AlgebraicGeometry

theorem ModularCurve.XOneP.exists_opens_hom_mapsTo_irreducibleComponents_pullback_modelTo_zmod_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    [Algebra A (ZMod p)] :
    ∃ (U : (pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p))).Opens)
      (φ : (U : Scheme) ⟶ pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p))),
      φ ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) =
        U.ι ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p)) ∧
      (∀ x : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p))), x ∉ U →
        (∃ _ : IsDomain ((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p))).presheaf.stalk x),
          IsDiscreteValuationRing ((pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p))).presheaf.stalk x)) ∧
        ∃ y : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p))), y ∈ U ∧ y ⤳ x) ∧
      ∀ Z ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p))),
        ∃ Z' ∈ irreducibleComponents ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A (ZMod p))), Z' ≠ Z ∧ Set.MapsTo φ.base (U.ι.base ⁻¹' Z) Z' := by sorry
