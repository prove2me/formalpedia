-- Prove2me | Theorems.Thm_IsLocalRing_isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective
-- name    : IsLocalRing.isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/8537e5d9-9c57-54c9-a533-a53a8206c861
-- title:
--   Residue field, units and square-zero kernel along a small surjection
-- statement:
--   Let $B$ and $B'$ be commutative local rings in a common universe, and let $\sigma : B' \to B$ be a ring homomorphism which is surjective as a function and satisfies $(\ker \sigma)\cdot \mathfrak m_{B'} = 0$, where $\mathfrak m_{B'}$ is the maximal ideal of $B'$. Let $p$ be a prime number such that the residue field of $B$ has characteristic $p$ and is algebraically closed, and let $q, q'$ be prime numbers with $p \neq q$ and $p \neq q'$. The conclusion is the conjunction of four assertions: the residue field of $B'$ is algebraically closed; it has characteristic $p$; the image of the natural number $q q'$ in $B'$ is a unit; and $(\ker \sigma)\cdot(\ker \sigma) = 0$. Note that the hypothesis $(\ker\sigma)\cdot\mathfrak m_{B'} = 0$ is used only for the last assertion, while the two primes $q, q'$ enter only through the unit assertion.
--
--   This is the standard transfer of residue-field data along a small surjection of local rings, together with the observation that primes different from the residue characteristic are invertible and that a small surjection has square-zero kernel. It is used in the construction of fake elliptic curves over the Čerednik–Drinfeld deformation rings, in [`CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_of_surjective_of_ker_mul_maximalIdeal_eq_bot_of_ne_of_isAlgClosed`](thm.html#CerednikDrinfeld.QM.FakeEllipticCurve.exists_isPullbackVia_of_surjective_of_ker_mul_maximalIdeal_eq_bot_of_ne_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

universe u

theorem IsLocalRing.isAlgClosed_residueField_and_charP_and_isUnit_and_ker_mul_ker_of_surjective
    {B B' : Type u} [CommRing B] [IsLocalRing B] [CommRing B'] [IsLocalRing B']
    (σ : B' →+* B) (hσ : Function.Surjective σ) (hsmall : RingHom.ker σ * maximalIdeal B' = ⊥)
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField B) p] [IsAlgClosed (ResidueField B)]
    (q q' : ℕ) [Fact q.Prime] [Fact q'.Prime] (hpq : p ≠ q) (hpq' : p ≠ q') :
    IsAlgClosed (ResidueField B') ∧ CharP (ResidueField B') p ∧
      IsUnit ((q * q' : ℕ) : B') ∧ RingHom.ker σ * RingHom.ker σ = ⊥ := by sorry
