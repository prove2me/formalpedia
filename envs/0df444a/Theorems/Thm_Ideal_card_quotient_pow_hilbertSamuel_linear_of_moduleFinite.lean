-- Prove2me | Theorems.Thm_Ideal_card_quotient_pow_hilbertSamuel_linear_of_moduleFinite
-- name    : Ideal.card_quotient_pow_hilbertSamuel_linear_of_moduleFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/f753a322-715b-5558-bce3-d1bdc75d441c
-- title:
--   Linear growth of #(R/I^m) for R finite over ℤ
-- statement:
--   Let $R$ be a commutative ring which is finite as a $\mathbb{Z}$-module, let $I$ be an ideal of $R$, and let $q$ be a natural number which is prime (supplied as a `Fact` instance) with the image of $q$ in $R$ lying in $I$. The assertion is that there exist natural numbers $e$ and $C$ such that for every natural number $m$ both
--   $$\#(R/I^m) \le q^{me+C} \qquad\text{and}\qquad q^{me} \le \#(R/I^m)\cdot q^{C}$$
--   hold, the cardinalities being taken as `Nat.card` of the quotient ring $R/I^m$ (so that the value is $0$ if the quotient is infinite, and $1$ for the zero ring). Thus a single slope $e$ serves for the upper and the lower bound, with a single additive constant $C$, uniformly in $m$; equivalently $\log_q \#(R/I^m) = me + O(1)$. No information about the value of $e$ or $C$ beyond their existence is asserted, and the statement includes the case $m=0$.
--
--   This is Hilbert–Samuel linearity for a ring of Krull dimension at most one, phrased without localisation or completion and in point-count rather than length form; $e$ is the corresponding multiplicity. It is used for bounding indices of torsion subgroups cut out by powers of an ideal, and in particular in the linear-growth estimate for the Néron-type torsion sheaf attached to the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_card_quotient_pow_hilbertSamuel_linear_of_moduleFinite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Ideal.card_quotient_pow_hilbertSamuel_linear_of_moduleFinite
    (R : Type*) [CommRing R] [Module.Finite ℤ R]
    (I : Ideal R) (q : ℕ) [Fact q.Prime] (hqI : (q : R) ∈ I) :
    ∃ e C : ℕ, ∀ m : ℕ,
      Nat.card (R ⧸ I ^ m) ≤ q ^ (m * e + C) ∧
        q ^ (m * e) ≤ Nat.card (R ⧸ I ^ m) * q ^ C := by sorry
