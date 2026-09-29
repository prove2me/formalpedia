-- Prove2me | Theorems.Thm_ModularCurve_JZero_degree_erase_cuspInftyBar
-- name    : ModularCurve.JZero.degree_erase_cuspInftyBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/75de3a2b-7e79-5315-9eef-25779e8bedc6
-- title:
--   Degree of the off-cusp part equals off-cusp mass
-- statement:
--   Let $N$ be a natural number, nonzero, and let $\bar F_N$ denote `modularFunctionFieldBar N`, the intermediate field of $\overline{\mathbb Q}((q))$ obtained by adjoining to $\overline{\mathbb Q}$ the coefficientwise images of the elements of `modularFunctionFieldFull N` $= \mathbb Q(\text{divisorExpansions } N) \subseteq \mathbb Q((q))$. Let $D$ be a divisor of $\bar F_N$ over $\overline{\mathbb Q}$, i.e. a finitely supported function from the places of $\bar F_N/\overline{\mathbb Q}$ (valuation subrings containing $\overline{\mathbb Q}$, proper, with principal ideals) to $\mathbb Z$. Write $\bar\infty$ for `cuspInftyBar N`, the place attached to the valuation subring of $q$-integral elements, the required element of $q$-order $-1$ being the $q$-expansion of $j$. The assertion is that the degree of the divisor $D$ with its coefficient at $\bar\infty$ deleted — degree being the sum of $D(v)\cdot\deg v$ over the remaining places — equals `offBaseMass N D`, defined as the plain sum $\sum_{v\neq\bar\infty} D(v)$ of the coefficients of that same divisor.
--
--   A bookkeeping identity translating between the degree of a divisor on $X_0(N)$ over $\overline{\mathbb Q}$, the quantity occurring in Riemann–Roch, and the unweighted sum of its coefficients away from the cusp $\bar\infty$, the quantity occurring in the height form on $J_0(N)$. It is used in the Riemann–Roch estimates for off-cusp divisors, namely [`ModularCurve.JZero.finrank_riemannRochSpace_canonicalDivisorOf_sub_erase_add_offBaseMass`](thm.html#ModularCurve.JZero.finrank_riemannRochSpace_canonicalDivisorOf_sub_erase_add_offBaseMass) and [`ModularCurve.JZero.offBaseMass_le_genusFF_of_riemannRochSpace_eq_bot`](thm.html#ModularCurve.JZero.offBaseMass_le_genusFF_of_riemannRochSpace_eq_bot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_degree_erase_cuspInftyBar.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.degree_erase_cuspInftyBar (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Divisor.degree (D.erase (cuspInftyBar N)) = offBaseMass N D := by sorry
