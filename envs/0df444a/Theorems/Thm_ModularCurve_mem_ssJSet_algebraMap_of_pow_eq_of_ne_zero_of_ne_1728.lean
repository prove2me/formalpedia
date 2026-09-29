-- Prove2me | Theorems.Thm_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_zero_of_ne_1728
-- name    : ModularCurve.mem_ssJSet_algebraMap_of_pow_eq_of_ne_zero_of_ne_1728
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/1cddc0fd-edf3-5185-899b-69ee51c10bea
-- title:
--   Supersingularity of j with j^{q^2}=j under base change
-- statement:
--   Let $q$ be a prime and let $k$ and $K$ be fields of characteristic $q$ with $K$ a $k$-algebra and $K$ algebraically closed (decidable equality on $k$ and $K$ being assumed for the torsion predicate). Assume that every $x \in K$ satisfying $x^{q^n} = x$ for some $n > 0$ lies in the image of the structure map $k \to K$; that is, the relative algebraic closure of $\mathbb{F}_q$ inside $K$ is contained in the image of $k$. Let $a \in k$ be such that $a$ belongs to $\mathrm{ssJSet}\ q\ k$, meaning: for every Weierstrass curve $W$ over $k$ which is elliptic and has $j$-invariant $W.j = a$, every point $P$ of the associated affine curve with $q \cdot P = 0$ is zero. Assume further $a^{q^2} = a$, that $q \ge 5$, and that $a \ne 0$ and $a \ne 1728$. Then the image $\mathrm{algebraMap}\ k\ K\ a$ belongs to $\mathrm{ssJSet}\ q\ K$: every elliptic Weierstrass curve over $K$ with $j$-invariant equal to that image has no nonzero $K$-point killed by $q$.
--
--   The set $\mathrm{ssJSet}\ q\ F$ collects those $j$-invariants all of whose elliptic models over $F$ have no nonzero $F$-rational $q$-torsion; over an algebraically closed field this is Deuring's notion of a supersingular $j$-invariant, detected by the vanishing of the Hasse invariant. The present statement transports this property from a value $a$ in the prime field's quadratic extension inside $k$ to its image in an algebraically closed extension $K$, under the restrictions $q \ge 5$ and $a \ne 0, 1728$ which allow the two models to be compared by an explicit variable change; it is used in the study of the plane model of $X_0(q)$ at a supersingular point, by [`ModularCurve.eq_of_isPrime_of_liesOver_descendedNodeRing_of_ne_zero_of_ne_1728`](thm.html#ModularCurve.eq_of_isPrime_of_liesOver_descendedNodeRing_of_ne_zero_of_ne_1728), [`ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728`](thm.html#ModularCurve.exists_crossingPresentation_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728) and [`ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728`](thm.html#ModularCurve.isIntegrallyClosed_modularLocalizedAtPoint_coeffSubring_of_ne_zero_of_ne_1728).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_ssJSet_algebraMap_of_pow_eq_of_ne_zero_of_ne_1728.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_SupersingularNodes
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_GluedPic0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.mem_ssJSet_algebraMap_of_pow_eq_of_ne_zero_of_ne_1728
    {q : ℕ} [Fact q.Prime] {k K : Type*} [Field k] [Field K] [CharP k q] [CharP K q] [DecidableEq k] [DecidableEq K]
    [Algebra k K] [IsAlgClosed K]
    (hk : ∀ x : K, (∃ n : ℕ, 0 < n ∧ x ^ (q ^ n) = x) → x ∈ (algebraMap k K).range)
    (a : k) (ha : a ∈ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (hq : 5 ≤ q) (h0 : a ≠ 0) (h1728 : a ≠ 1728) :
    algebraMap k K a ∈ ssJSet q K := by sorry
