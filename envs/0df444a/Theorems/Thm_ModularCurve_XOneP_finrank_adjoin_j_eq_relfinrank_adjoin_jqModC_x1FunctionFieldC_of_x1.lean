-- Prove2me | Theorems.Thm_ModularCurve_XOneP_finrank_adjoin_j_eq_relfinrank_adjoin_jqModC_x1FunctionFieldC_of_x1
-- name    : ModularCurve.XOneP.finrank_adjoin_j_eq_relfinrank_adjoin_jqModC_x1FunctionFieldC_of_x1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/dbb60cec-7267-52be-8e8b-d8bee15fa285
-- title:
--   Degree over the j-line unchanged on reduction at p
-- statement:
--   Let $p$ be a prime and $M \ge 5$ an integer with $p \nmid M$. Let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of type $\{p\}$, and let $\zeta \in L$ be a primitive $p$-th root of unity. Let $K$ be an intermediate field of $L \subseteq L((q))$ (Laurent series over $L$) which equals [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L((q))$ generated over $L$ by the image, under the coefficientwise map $\mathbb{Q}((q)) \to L((q))$ induced by $\mathbb{Q} \to L$, of the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios `intFormRatiosC` of integral forms of equal weight on $\Gamma_1(M)$. Let $A$ be a discrete valuation domain with $L$ as fraction field, such that $p$ lies in the maximal ideal of $A$ and $\zeta$ lies in the image of $A \to L$, with $K$ an $A$-algebra compatibly with $A \to L \to K$. Let $j \in K$ be an element whose image in $L((q))$ is the coefficientwise image of $q^{-1}\bigl(E_4^{3}\,\eta^{-24}\bigr)$, the $q$-expansion [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), and assume $j \neq 0$. Write $\kappa$ for the residue field of $A$. Then the degree of $K$ over the intermediate field $L(j)$ equals the relative degree, in the sense of `IntermediateField.relfinrank` (the degree of the second field over the intersection of the two), of the subfield of $\kappa((q))$ generated over $\kappa$ by [`ModularCurve.jqModC`](def/ModularCurve_JqCoeff.html#L15) $\kappa = q^{-1}\bigl(E_4^{3}\,\eta^{-24}\bigr)$ read with coefficients in $\kappa$, inside the subfield [`ModularCurve.x1FunctionFieldC`](def/ModularCurve_X1.html#L134) $\kappa$ $M$ of $\kappa((q))$ generated over $\kappa$ by the ratios `intFormRatiosC` for $\Gamma_1(M)$.
--
--   This is the numerical form of good reduction of $X_1(M)$ at a prime $p$ not dividing the level: the degree of the $q$-expansion field of level $M$ over the $j$-line does not drop when passing from characteristic zero (over a field containing $\zeta_p$) to the residue characteristic $p$. It feeds the analysis of the valuation subrings of the level-$M$ function field in [`ModularCurve.XOneP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul`](thm.html#ModularCurve.XOneP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul) and its $\Gamma_0$ counterpart, where the Gauss valuation of $L(j)$ is shown to have a single unramified extension to $K$ whose residue field is the characteristic-$p$ function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_finrank_adjoin_j_eq_relfinrank_adjoin_jqModC_x1FunctionFieldC_of_x1.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XOneP.finrank_adjoin_j_eq_relfinrank_adjoin_jqModC_x1FunctionFieldC_of_x1
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    Module.finrank ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K =
      IntermediateField.relfinrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({ModularCurve.jqModC (IsLocalRing.ResidueField A)} : Set (LaurentSeries (IsLocalRing.ResidueField A))))
        (ModularCurve.x1FunctionFieldC (IsLocalRing.ResidueField A) M) := by sorry
