-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_intCoeffs_jq_pow
-- name    : ModularCurve.PhiGen.intCoeffs_jq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/0fd49a9c-a236-5401-8f05-75d28d692638
-- title:
--   Powers of j have integral q-expansions
-- statement:
--   For every natural number $n$, the Laurent series $\mathtt{jq}^n$ over $\mathbb{Q}$ satisfies the predicate `IntCoeffs`, that is: for every integer $m$ there is an integer $z$ with $m$-th coefficient of $\mathtt{jq}^n$ equal to the image of $z$ in $\mathbb{Q}$. Here `jq` is the Laurent series (Hahn series over $\mathbb{Z}$ with coefficients in $\mathbb{Q}$) obtained as the product of the monomial $q^{-1}$, namely `HahnSeries.single (-1 : ℤ) 1`, with the Laurent series attached to the power series `jNumQ`, the base change along $\mathbb{Z} \to \mathbb{Q}$ of the integral power series `jNum`; thus `jq` is $q^{-1}$ times a power series all of whose coefficients are integers, and the assertion is that the same integrality holds for each coefficient of each of its powers $\mathtt{jq}^n$, including $n = 0$, where the series is $1$. No hypotheses beyond the natural number $n$ are imposed.
--
--   This is the integrality of the $q$-expansion coefficients of powers of the modular invariant $j$, whose expansion $q^{-1} + 744 + \dots$ has integer coefficients. It serves as the base case for integrality statements about polynomial expressions in $j$, and is used in [`ModularCurve.exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits`](thm.html#ModularCurve.exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits) and in [`ModularCurve.exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits_of_forall_ord_neg`](thm.html#ModularCurve.exists_smul_forall_coeff_mem_and_exists_not_mem_nonunits_of_forall_ord_neg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_intCoeffs_jq_pow.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.intCoeffs_jq_pow (n : ℕ) : IntCoeffs (jq ^ n) := by sorry
