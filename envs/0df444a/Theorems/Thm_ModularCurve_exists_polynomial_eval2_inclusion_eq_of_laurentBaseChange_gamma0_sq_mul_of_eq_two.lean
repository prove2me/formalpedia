-- Prove2me | Theorems.Thm_ModularCurve_exists_polynomial_eval2_inclusion_eq_of_laurentBaseChange_gamma0_sq_mul_of_eq_two
-- name    : ModularCurve.exists_polynomial_eval2_inclusion_eq_of_laurentBaseChange_gamma0_sq_mul_of_eq_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/97a23132-23b8-5dbe-b56c-7b22c91e2680
-- title:
--   At q=2, K(Γ₀(q²M'))=K₀[j(q²τ)]
-- statement:
--   Fix a prime $q$ with $q=2$, a nonzero natural number $M'$ with $q \nmid M'$, and a field $L$ of characteristic zero that is algebraic over $\mathbb{Q}$. Inside the Laurent series field $\mathrm{LaurentSeries}\ L$, let $K$ be the $L$-intermediate field `laurentBaseChange L (qExpFunctionFieldC ℚ (Gamma0 (q ^ 2 * M')))`, that is, the subfield generated over $L$ by the coefficientwise image under $\mathbb{Q} \to L$ of the subfield of $\mathbb{Q}(\!(\mathsf q)\!)$ obtained by adjoining to $\mathbb{Q}$ all quotients $\,\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ coming from two modular forms $f,g$ of one and the same weight $k$ for $\Gamma_0(q^2M')$ whose $q$-expansions are the integral power series $p_f,p_g$, with nonvanishing denominator; let $K_0$ be the corresponding field for $\Gamma_0(M')$, and assume $K_0 \le K$. Let $j \in K$ be the element whose image in $\mathrm{LaurentSeries}\ L$ is the coefficientwise image of `jq` $=\mathsf q^{-1}\cdot \mathrm{jNumQ}$, and let $J_2 \in K$ be the element whose image is the coefficientwise image of `jqN (q ^ 2)`, the series obtained from `jq` by multiplying all exponents by $q^2$. Then for every $x \in K$ there is a polynomial $p$ with coefficients in $K_0$ whose evaluation at $J_2$, along the inclusion $K_0 \hookrightarrow K$, equals $x$.
--
--   This is the statement that the $q$-expansion function field of $X_0(q^2M')$ over $L$ is generated, indeed as a polynomial ring image, over that of $X_0(M')$ by the function $j(q^2\tau)$, here in the case $q=2$; the companion statement covers $q \ge 5$. It is used in the computation of the ramification index along the inclusion of the level-$M'$ field into the level-$q^2M'$ field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_polynomial_eval2_inclusion_eq_of_laurentBaseChange_gamma0_sq_mul_of_eq_two.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open scoped MatrixGroups

theorem ModularCurve.exists_polynomial_eval2_inclusion_eq_of_laurentBaseChange_gamma0_sq_mul_of_eq_two
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L] [Algebra.IsAlgebraic ℚ L]

    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q ^ 2 * M'))))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)

    (J₂ : ↥K) (hJ₂ : ((J₂ : LaurentSeries L)) = ModularCurve.coeffEmb L (ModularCurve.jqN (q ^ 2)))

    (K₀ : IntermediateField L (LaurentSeries L))
    (hK₀ : K₀ = ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')))
    (hle₀ : K₀ ≤ K)
    (x : ↥K) :
    ∃ p : Polynomial ↥K₀, Polynomial.eval₂ (IntermediateField.inclusion hle₀).toRingHom J₂ p = x := by sorry
