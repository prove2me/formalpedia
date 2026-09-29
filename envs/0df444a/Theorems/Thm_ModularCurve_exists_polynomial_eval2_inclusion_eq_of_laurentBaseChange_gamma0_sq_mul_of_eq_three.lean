-- Prove2me | Theorems.Thm_ModularCurve_exists_polynomial_eval2_inclusion_eq_of_laurentBaseChange_gamma0_sq_mul_of_eq_three
-- name    : ModularCurve.exists_polynomial_eval2_inclusion_eq_of_laurentBaseChange_gamma0_sq_mul_of_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/f179c8cc-ccb6-53e0-97b3-9ed9fa93e927
-- title:
--   K₀[j(q²τ)] = K for X₀(q²M'), case q=3
-- statement:
--   Let $q$ be a prime with $q = 3$, let $M'$ be a nonzero natural number with $q \nmid M'$, and let $L$ be a field of characteristic zero that is algebraic over $\mathbb{Q}$. Inside the Laurent series field $L(\!(\mathsf q)\!)$ consider two intermediate fields over $L$: $K$, assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q ^ 2 * M')))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the field generated over $L$ by the coefficientwise image under $\mathbb{Q} \to L$ of the subfield of $\mathbb{Q}(\!(\mathsf q)\!)$ generated over $\mathbb{Q}$ by all quotients $\mathrm{int}(p_f)/\mathrm{int}(p_g)$ attached to pairs of modular forms $f, g$ of a common weight $k$ for $\Gamma_0(q^2M')$ with integral $q$-expansions $p_f, p_g$ and $\mathrm{int}(p_g) \ne 0$; and $K_0$, the same construction for $\Gamma_0(M')$, assumed to satisfy $K_0 \le K$. Let $j \in K$ have underlying Laurent series the image under the coefficient map of $\mathsf q^{-1}$ times the integral power series $\mathrm{jNum}$, and let $J_2 \in K$ have underlying Laurent series the image of that series after the substitution $\mathsf q \mapsto \mathsf q^{q^2}$. Then for every $x \in K$ there is a polynomial $p$ with coefficients in $K_0$ such that evaluating $p$ at $J_2$, along the inclusion $K_0 \hookrightarrow K$, gives $x$; that is, $K = K_0[J_2]$.
--
--   This is the statement that the $q$-expansion function field of $X_0(q^2M')$ over $L$ is generated, as a ring, over that of $X_0(M')$ by the function $j(q^2\tau)$, here in the case $q = 3$ (the companion statement covers $q \ge 5$). It is used in the computation of the ramification index along the inclusion of the level-$M'$ field into the level-$q^2M'$ field in terms of the order of $j(q^2\tau)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_polynomial_eval2_inclusion_eq_of_laurentBaseChange_gamma0_sq_mul_of_eq_three.lean

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

theorem ModularCurve.exists_polynomial_eval2_inclusion_eq_of_laurentBaseChange_gamma0_sq_mul_of_eq_three
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
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
