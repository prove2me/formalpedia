-- Prove2me | Theorems.Thm_ModularCurve_XOneP_relfinrank_laurentBaseChange_x1FunctionField_le_x1_mul
-- name    : ModularCurve.XOneP.relfinrank_laurentBaseChange_x1FunctionField_le_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:48.546916+00:00
-- url     : https://prove2.me/theorems/28d242b4-c2fc-5169-a3ff-bf6f0a382521
-- title:
--   Relative degree of X₁(Mp) over X₁(M) at most p²-1
-- statement:
--   Let $p$ be a prime, let $M\ge 5$ be a natural number with $p\nmid M$, and let $L$ be a field of characteristic zero which is a cyclotomic extension of $\mathbb{Q}$ of order $\{p\}$, together with a primitive $p$-th root of unity $\zeta\in L$. Inside the Laurent series field $L((q))$, let $K$ be the intermediate field over $L$ given by $\mathrm{laurentBaseChange}$ of the $q$-expansion function field of level $Mp$: that is, $K$ is generated over $L$ by the image, under the coefficientwise ring map $L((q))\leftarrow\mathbb{Q}((q))$ induced by $\mathbb{Q}\to L$, of the field $\mathrm{x1FunctionField}(Mp)=\mathrm{qExpFunctionFieldC}\,\mathbb{Q}\,(\Gamma_1(Mp))\subseteq\mathbb{Q}((q))$. Let $A$ be a discrete valuation ring which is a domain with an $A$-algebra structure on $L$ making $L$ its fraction field, assume $p$ lies in the maximal ideal of $A$ and that $\zeta$ is in the image of $A\to L$, and let $K$ be an $A$-algebra compatibly with the tower $A\to L\to K$. Let $j\in K$ be a nonzero element whose image in $L((q))$ is the coefficientwise image of $q^{-1}$ times the power series $\mathrm{jNumQ}$ over $\mathbb{Q}$, i.e. the $q$-expansion of the modular $j$-invariant. Then the relative degree of $K$ over the corresponding base-changed $q$-expansion function field of level $M$, namely $L\cdot\mathbb{Q}(X_1(M))\subseteq L((q))$, is at most $p^2-1$; since the latter field is contained in $K$, this relative rank is the field degree $[K:L\cdot\mathbb{Q}(X_1(M))]$.
--
--   Classically the degree equals the index $[\Gamma_1(M):\Gamma_1(Mp)]=p^2-1$; only the upper bound is asserted, which is the direction consumed by the fundamental identity $\sum_i e_if_i\le[K:K_M]$ when counting the places of $X_1(Mp)$ above a place of $X_1(M)$. It is used in the local analysis at $p$ of the $q$-expansion function fields of $X_1(Mp)$ and $X_1(Mp)/\Gamma_0(p)$-type models, by [`ModularCurve.XOneP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul`](thm.html#ModularCurve.XOneP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_relfinrank_gaussReduction_x1_mul) and [`ModularCurve.XOneGammaZeroP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_gaussReduction_eq_x1x0`](thm.html#ModularCurve.XOneGammaZeroP.valuationSubring_eq_or_eq_comap_and_uniformizer_and_gaussReduction_eq_x1x0).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_relfinrank_laurentBaseChange_x1FunctionField_le_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem ModularCurve.XOneP.relfinrank_laurentBaseChange_x1FunctionField_le_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)] :
    IntermediateField.relfinrank (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M)) K ≤ p ^ 2 - 1 := by sorry
