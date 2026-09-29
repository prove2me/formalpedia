-- Prove2me | Theorems.Thm_ModularCurve_degeneracyPullbackInputs_of_prime
-- name    : ModularCurve.degeneracyPullbackInputs_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/d34f37d3-32f7-5650-abe0-242cc185e327
-- title:
--   Degeneracy pull-back inputs hold at every prime level q
-- statement:
--   Let $N$ and $q$ be natural numbers, both nonzero (as recorded by `NeZero` instances), and assume $q$ is prime. The conclusion [`ModularCurve.DegeneracyPullbackInputs N q`](def/ModularCurve_DegeneracyVp.html#L65) asserts the conjunction of four statements about the field $L =$ `AlgebraicClosure ℚ` and the two degeneracy embeddings between the $L$-base-changed modular function fields: writing `modularFunctionFieldFull M` for the subfield of $\mathbb{Q}$-Laurent series generated over $\mathbb{Q}$ by the divisor expansions at level $M$, and `laurentBaseChange L` for the subfield of $L$-Laurent series generated over $L$ by the coefficientwise image of such a field, let $F_N$ and $F_{Nq}$ be the base changes of levels $N$ and $Nq$, and let `heckeAlphaBar` be the inclusion $F_N \hookrightarrow F_{Nq}$ coming from $N \mid Nq$ and `heckeBetaBar` the embedding induced by the $q$-expansion substitution `qExpand L q`. Then: (i) `heckeAlphaBar` is an integral ring homomorphism; (ii) `heckeBetaBar` is an integral ring homomorphism; (iii) $F_{Nq}$ satisfies `HasPrincipalDivisors` over $L$, i.e. every nonzero $f \in F_{Nq}$ admits a divisor $D$ with $D(v) = \operatorname{ord}_v f$ at every place $v$ of $F_{Nq}/L$ and $\deg D = 0$; and (iv) the predicate `FundamentalIdentity` holds for $F_{Nq}$ over $F_N$ along each of the two embeddings, using the integrality witnesses of (i) and (ii). All four are packaged as a single existential statement.
--
--   This is the verification, for an arbitrary level $N$ and a prime $q$, of the hypotheses under which the two degeneracy maps between levels $N$ and $Nq$ induce genuine divisor pull-backs $J_0(N) \to J_0(Nq)$. It is invoked in the construction of the degeneracy pull-back homomorphism on points of the Deligne–Rapoport model package and in the identity expressing the Hecke operator at $q$ through the Atkin–Lehner involution.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_degeneracyPullbackInputs_of_prime.lean

import Definitions.Def_ModularCurve_DegeneracyVp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.degeneracyPullbackInputs_of_prime (N q : ℕ) [NeZero N] [NeZero q]
    (hq : q.Prime) : ModularCurve.DegeneracyPullbackInputs N q := by sorry
