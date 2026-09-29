-- Prove2me | Theorems.Thm_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_two
-- name    : ModularCurve.mem_ssJSet_algebraMap_of_pow_eq_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/d368ab1f-8f37-572d-a63e-bd2afe6579db
-- title:
--   Supersingular j-values persist over algebraically closed extensions
-- statement:
--   Let $q$ be a prime with $q \neq 2$, and let $k$ and $K$ be fields of characteristic $q$ with $K$ a $k$-algebra and $K$ algebraically closed. Assume that every $x \in K$ satisfying $x^{q^n} = x$ for some $n > 0$ lies in the range of the structure map $k \to K$, i.e. all elements of $K$ algebraic over the prime field come from $k$. Let $a \in k$ satisfy $a^{q^2} = a$, and assume that $a$ lies in $\mathrm{ssJSet}\ q\ k$, that is: for every Weierstrass curve $W$ over $k$ which is elliptic and has $j$-invariant $W.j = a$, every point $P$ of the associated affine curve with $q \bullet P = 0$ is zero. The conclusion is that the image of $a$ in $K$ lies in $\mathrm{ssJSet}\ q\ K$: every elliptic Weierstrass curve over $K$ with $j$-invariant $\mathrm{algebraMap}\ k\ K\ a$ has no nonzero $q$-torsion point. No restriction such as $a \neq 0, 1728$ is imposed.
--
--   This is the statement that supersingularity of a $j$-value, formulated as absence of nonzero $q$-torsion on every elliptic curve with that $j$-invariant, is inherited by an algebraically closed extension whose algebraic-over-$\mathbb{F}_q$ elements already lie in the base field. It is used in the analysis of modular and $\lambda$-level curves at supersingular points, for instance by [`ModularCurve.isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring`](thm.html#ModularCurve.isIntegrallyClosed_lambdaLocalizedAtPoint_coeffSubring) and by the identifications of completed local rings with crossing models; the proof cites the criterion [`WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero`](thm.html#WeierstrassCurve.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero) expressing $q$-torsion freeness by vanishing of the Hasse invariant for $q$ odd, together with its transformation rule under variable changes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_two.lean

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.mem_ssJSet_algebraMap_of_pow_eq_of_ne_two
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {k K : Type*} [Field k] [Field K] [CharP k q] [CharP K q]
    [DecidableEq k] [DecidableEq K] [Algebra k K] [IsAlgClosed K]
    (hk : ∀ x : K, (∃ n : ℕ, 0 < n ∧ x ^ (q ^ n) = x) → x ∈ (algebraMap k K).range)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a) :
    algebraMap k K a ∈ ssJSet q K := by sorry
