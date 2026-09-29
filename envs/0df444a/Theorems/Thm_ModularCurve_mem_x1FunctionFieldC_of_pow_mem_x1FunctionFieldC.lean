-- Prove2me | Theorems.Thm_ModularCurve_mem_x1FunctionFieldC_of_pow_mem_x1FunctionFieldC
-- name    : ModularCurve.mem_x1FunctionFieldC_of_pow_mem_x1FunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/e4d78843-09d7-5518-a8de-df72318d2aa1
-- title:
--   The q-expansion field of X₁(M) is closed under p-th roots
-- statement:
--   Let $p$ be a prime and let $M$ be a nonzero natural number with $5 \le M$ and $p \nmid M$. Let $k$ be an algebraically closed field of characteristic $p$, and write $k(\!(q)\!)$ for the field `LaurentSeries k` of formal Laurent series over $k$. Inside $k(\!(q)\!)$ consider the intermediate field [`ModularCurve.x1FunctionFieldC k M`](def/ModularCurve_X1.html#L134), namely [`ModularCurve.qExpFunctionFieldC k (Gamma1 M)`](def/ModularCurve_X1.html#L101), which by definition is the subfield of $k(\!(q)\!)$ obtained by adjoining to $k$ the set `intFormRatiosC k (Gamma1 M)` of $q$-expansions attached to $\Gamma_1(M)$. The assertion is: for every Laurent series $y \in k(\!(q)\!)$, if $y^p$ lies in this field, then $y$ itself lies in it. Equivalently, [`ModularCurve.x1FunctionFieldC k M`](def/ModularCurve_X1.html#L134) is closed under the (unique) $p$-th roots existing in $k(\!(q)\!)$; since $k(\!(q)\!)$ has no nontrivial $p$-th roots of unity in characteristic $p$, the $p$-power map is injective and the hypothesis determines $y$ uniquely.
--
--   The statement says that the $q$-expansion function field of $X_1(M)$ over an algebraically closed field of characteristic $p$ is relatively perfect in $k(\!(q)\!)$: no $p$-th root of one of its elements escapes it. It is used in the construction of Kummer-type generators for the degree-$p$ situation, specifically by [`ModularCurve.isKummerGenerator_one_hasseRootFn_of_charP_two`](thm.html#ModularCurve.isKummerGenerator_one_hasseRootFn_of_charP_two), and rests on the finiteness and separability of this field over $k(\bar\jmath)$ provided by [`ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC`](thm.html#ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_x1FunctionFieldC_of_pow_mem_x1FunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped IntermediateField

theorem ModularCurve.mem_x1FunctionFieldC_of_pow_mem_x1FunctionFieldC
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (y : LaurentSeries k) (hy : y ^ p ∈ ModularCurve.x1FunctionFieldC k M) :
    y ∈ ModularCurve.x1FunctionFieldC k M := by sorry
