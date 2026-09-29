-- Prove2me | Theorems.Thm_HenselianLocalRing_exists_isPrimitiveRoot_of_pow_sq_sub_one_eq
-- name    : HenselianLocalRing.exists_isPrimitiveRoot_of_pow_sq_sub_one_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/8bf131fb-977b-58d4-b709-b9ac65670af1
-- title:
--   Primitive q-th root of unity from a (q²-1)-st root of q
-- statement:
--   Let $q$ be a prime number and let $A$ be a commutative ring which is an integral domain, local, henselian, and whose residue field $A/\mathfrak{m}$ is algebraically closed. Assume that the image of $q$ in $A$ lies in the maximal ideal $\mathfrak{m}$ of $A$ and is nonzero, so that $A$ has residue characteristic $q$ while $q$ is not a zero divisor. Assume further that $q$ admits a $(q^2-1)$-st root in $A$, i.e. that there is an element $\pi \in A$ with $\pi^{q^2-1} = q$ (the exponent being the natural-number difference, which is harmless since $q \ge 2$). The conclusion is that there exists $\zeta \in A$ with `IsPrimitiveRoot ζ q`, that is, $\zeta^{q} = 1$ and every natural number $n$ with $\zeta^{n} = 1$ is divisible by $q$; in particular $\zeta \ne 1$, so $A$ contains a full set of $q$-th roots of unity.
--
--   This is the standard fact that a henselian local ring of residue characteristic $q$ with algebraically closed residue field acquires the $q$-th roots of unity as soon as $q$ becomes a $(q^2-1)$-st power, the model case being the extension $\mathbb{Q}_q(q^{1/(q^2-1)})$ of $\mathbb{Q}_q$, which contains $\mu_q$. It is used in the construction of admissible systems of small constants over a descent base for modular curves of full level, where a primitive $q$-th root of unity in the base ring is required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HenselianLocalRing_exists_isPrimitiveRoot_of_pow_sq_sub_one_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem HenselianLocalRing.exists_isPrimitiveRoot_of_pow_sq_sub_one_eq
    (q : ℕ) [hq : Fact q.Prime]
    (A : Type*) [CommRing A] [IsDomain A] [IsLocalRing A] [HenselianLocalRing A]
    [IsAlgClosed (ResidueField A)]
    (hqA : (q : A) ∈ maximalIdeal A) (hq0 : (q : A) ≠ 0)
    (π : A) (hπ : π ^ (q ^ 2 - 1) = (q : A)) :
    ∃ ζ : A, IsPrimitiveRoot ζ q := by sorry
