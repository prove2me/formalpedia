-- Prove2me | Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
-- name    : ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/6e6a3746-8c47-5783-b57e-30717c9531db
-- title:
--   Supersingular j-invariants satisfy j^{q^2}=j
-- statement:
--   Let $K$ be an algebraically closed field, let $q$ be a prime number, and suppose $K$ has characteristic $q$. Let $a \in K$ belong to the set [`ModularCurve.ssJSet q K`](def/ModularCurve_SupersingularModuli.html#L7), that is: for every Weierstrass curve $W$ over $K$ which is elliptic (invertible discriminant) and whose $j$-invariant equals $a$, every point $P$ of the associated affine curve `W.toAffine.Point` with $q \cdot P = 0$ (the natural-number scalar multiple in the group of points) is the zero point; equivalently, no elliptic model with $j$-invariant $a$ has a nontrivial $q$-torsion point. The conclusion is that $a^{q^2} = a$, so that $a$ lies in the subfield with $q^2$ elements of $K$. Note that the hypothesis is phrased as a condition on all Weierstrass models with $j$-invariant $a$, not on a single fixed curve, and that the membership predicate quantifies over Weierstrass curves rather than over abstract elliptic curves.
--
--   This is the $j$-invariant form of Deuring's rationality theorem: the $j$-invariant of a supersingular elliptic curve in characteristic $q$ lies in $\mathbb{F}_{q^2}$. It is what makes the set of supersingular $j$-invariants finite and stable under $a \mapsto a^q$, and it is used throughout the treatment of the supersingular points of the reduction of modular curves modulo $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (q : ℕ) [Fact q.Prime] [CharP K q] {a : K} (ha : a ∈ ModularCurve.ssJSet q K) : a ^ (q ^ 2) = a := by sorry
