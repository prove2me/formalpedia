-- Prove2me | Theorems.Thm_ModularCurve_subsingleton_jZero_two
-- name    : ModularCurve.subsingleton_jZero_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/90c05f51-170a-536d-9261-c50d85ac1d00
-- title:
--   Triviality of J₀(2)
-- statement:
--   The assertion is that the type `JZero 2` is a subsingleton, i.e. has at most one element. Here `JZero N` is, by definition, `Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar N)`, the quotient of the additive group of degree-zero divisors of the function field `modularFunctionFieldBar N` over the base field $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` by the subgroup of principal divisors (viewed as a subgroup of the degree-zero divisors); and `modularFunctionFieldBar N` is the base change to $\overline{\mathbb{Q}}$, inside the Laurent series field `LaurentSeries (AlgebraicClosure ℚ)`, of the modular function field `modularFunctionFieldFull N` of level $N$. The theorem is stated for the single level $N = 2$ and takes no arguments and no hypotheses beyond the ambient instances. Since the quotient carries a group structure, the conclusion says exactly that the degree-zero divisor class group at level $2$ — the Jacobian $J_0(2)$ in its divisor-class incarnation — is the trivial group, every degree-zero divisor being principal.
--
--   This is the classical fact that $X_0(2)$ has genus zero, so that its Jacobian $J_0(2)$ vanishes. It is used to dispose of the level-$2$ (equivalently $p = 2$) case in several statements about torsion in $J_0(N)$ and about prolongations of places, where the conclusion then holds trivially.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_subsingleton_jZero_two.lean

import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.subsingleton_jZero_two : Subsingleton (JZero 2) := by sorry
