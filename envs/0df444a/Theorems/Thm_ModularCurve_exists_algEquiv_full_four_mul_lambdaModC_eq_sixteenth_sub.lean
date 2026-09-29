-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_full_four_mul_lambdaModC_eq_sixteenth_sub
-- name    : ModularCurve.exists_algEquiv_full_four_mul_lambdaModC_eq_sixteenth_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/b894a87a-fc2a-566d-8f90-393e379f9775
-- title:
--   An involution with μ ↦ 1/16-μ at level 4q
-- statement:
--   Let $q$ be a prime with $q \neq 2$. Write $F_{4q}$ for `modularFunctionFieldFull (4 * q)`, the intermediate field of the Laurent series field $\mathrm{LaurentSeries}\,\mathbb{Q}$ over $\mathbb{Q}$ obtained by adjoining the set of all series $\mathrm{qExpand}_{\mathbb{Q}}\,d\,(jq)$ with $d$ a nonzero divisor of $4q$, where $\mathrm{qExpand}_{\mathbb{Q}}\,d$ is the ring endomorphism of Laurent series that multiplies all exponents by $d$. Let $\mu =$ `lambdaModC ℚ` be the coefficientwise image in $\mathrm{LaurentSeries}\,\mathbb{Q}$ of the explicit integral Laurent series `lambdaInt` $= q\,\eta\text{-product}^8 \cdot \mathrm{qExpand}\,4(\eta\text{-product}^{16}) \cdot \mathrm{qExpand}\,2(\text{inverse }\eta\text{-unit})$, and let `lambdaNModC ℚ q` $= \mathrm{qExpand}_{\mathbb{Q}}\,q\,(\mu)$ be its $q$-fold exponent rescaling. The assertion is that there exists a $\mathbb{Q}$-algebra automorphism $\tau$ of $F_{4q}$ such that: $\tau(\tau(x)) = x$ for all $x$; for every $x \in F_{4q}$ whose underlying Laurent series is $\mu$, the underlying series of $\tau(x)$ is $\mathrm{C}(1/16) - \mu$, the constant series $1/16$ minus $\mu$; and for every $x \in F_{4q}$ whose underlying series is $\mathrm{qExpand}_{\mathbb{Q}}\,q\,(\mu)$, the underlying series of $\tau(x)$ is $\mathrm{C}(1/16) - \mathrm{qExpand}_{\mathbb{Q}}\,q\,(\mu)$. The last two clauses are conditional on such elements existing in $F_{4q}$; no membership claim is made here.
--
--   Classically this is the Atkin–Lehner involution $W_4 = W_q \circ w_{4q}$ on the function field of level $4q$, which acts on the normalised Legendre modular function $\mu = \lambda/16$ by the anharmonic substitution $\lambda \mapsto 1-\lambda$, and commutes with the $q$-th degeneracy map. It is used in [`ModularCurve.minpoly_lambdaNModC_coeff_mem_adjoin`](thm.html#ModularCurve.minpoly_lambdaNModC_coeff_mem_adjoin).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_full_four_mul_lambdaModC_eq_sixteenth_sub.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LambdaSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_algEquiv_full_four_mul_lambdaModC_eq_sixteenth_sub (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) :
    ∃ τ : ↥(modularFunctionFieldFull (4 * q)) ≃ₐ[ℚ] ↥(modularFunctionFieldFull (4 * q)),
      (∀ x, τ (τ x) = x) ∧
      (∀ x : ↥(modularFunctionFieldFull (4 * q)), (x : LaurentSeries ℚ) = lambdaModC ℚ →
          ((τ x : ↥(modularFunctionFieldFull (4 * q))) : LaurentSeries ℚ) = HahnSeries.C (1 / 16 : ℚ) - lambdaModC ℚ) ∧
      (∀ x : ↥(modularFunctionFieldFull (4 * q)), (x : LaurentSeries ℚ) = lambdaNModC ℚ q →
          ((τ x : ↥(modularFunctionFieldFull (4 * q))) : LaurentSeries ℚ) = HahnSeries.C (1 / 16 : ℚ) - lambdaNModC ℚ q) := by sorry
