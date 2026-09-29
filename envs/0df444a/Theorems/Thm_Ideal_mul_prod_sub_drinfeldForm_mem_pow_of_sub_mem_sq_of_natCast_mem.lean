-- Prove2me | Theorems.Thm_Ideal_mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem
-- name    : Ideal.mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/968df4bf-3278-5e3b-bd95-1d75c4c2b77a
-- title:
--   Drinfeld-form congruence modulo 𝔪^{q+2} at every prime
-- statement:
--   Let $q$ be a prime number, $R$ a commutative ring and $\mathfrak m \subseteq R$ an ideal containing the image of $q$ under the canonical map $\mathbb N \to R$. Let $x_0, x_1$ be elements of $\mathfrak m$, and let $P : \mathbb Z/q\mathbb Z \to R$ be any family of elements of $R$ indexed by the residues modulo $q$, subject to the single requirement that for every $c \in \mathbb Z/q\mathbb Z$ one has $P(c) - (x_1 + \bar c\, x_0) \in \mathfrak m^2$, where $\bar c \in R$ denotes the image of the natural-number representative $c.\mathrm{val} \in \{0,\dots,q-1\}$ of $c$. The conclusion is the congruence
--   $$x_0 \prod_{c \in \mathbb Z/q\mathbb Z} P(c) \;\equiv\; x_0 x_1^{\,q} - x_0^{\,q} x_1 \pmod{\mathfrak m^{\,q+2}},$$
--   that is, the difference $x_0\left(\prod_{c} P(c)\right) - (x_0 x_1^{q} - x_0^{q} x_1)$ lies in $\mathfrak m^{q+2}$. No hypothesis is placed on $R$ beyond commutativity, and $\mathfrak m$ need not be maximal, prime or proper; only $q \in \mathfrak m$, $x_0, x_1 \in \mathfrak m$ and the $q$ congruences modulo $\mathfrak m^2$ are assumed.
--
--   This is the algebraic identity underlying the comparison, modulo the square of the maximal ideal, between a product of Drinfeld-basis parameters and the Drinfeld form $x_0 x_1^{q} - x_0^{q} x_1$; note that it requires only $q \in \mathfrak m$, rather than the stronger divisibility that would exclude small $q$. It is used in the identification of a suitable completed local ring with a power series ring, in [`FormalGroup.IsDrinfeldBasisAdic.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_isRegularLocalRing_of_prime`](thm.html#FormalGroup.IsDrinfeldBasisAdic.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_isRegularLocalRing_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq_of_natCast_mem
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] (𝔪 : Ideal R) (hq : ((q : ℕ) : R) ∈ 𝔪)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ 𝔪) (hx₁ : x₁ ∈ 𝔪)
    (P : ZMod q → R) (hP : ∀ c : ZMod q, P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ 𝔪 ^ 2) :
    x₀ * (∏ c : ZMod q, P c) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ 𝔪 ^ (q + 2) := by sorry
