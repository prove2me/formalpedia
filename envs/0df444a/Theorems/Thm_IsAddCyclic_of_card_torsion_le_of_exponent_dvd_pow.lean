-- Prove2me | Theorems.Thm_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow
-- name    : IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/ba12501b-07b0-536d-b662-2cf87846df6d
-- title:
--   Finite abelian p-group with socle of order ≤ p is cyclic
-- statement:
--   Let $G$ be an additive commutative group whose underlying type is finite, let $p$ be a prime and let $m$ be a natural number. Assume that $p^m$ annihilates $G$, i.e. $p^m \cdot x = 0$ for every $x \in G$, and that the $p$-torsion is small: the cardinality (as computed by `Nat.card` on the subtype $\{x \in G : p\cdot x = 0\}$) is at most $p$. The conclusion is the conjunction of two assertions: first, $G$ is cyclic in the additive sense, `IsAddCyclic G`, i.e. there is an element whose multiples exhaust $G$; second, $\operatorname{card} G$ divides $p^m$. Note that finiteness is a hypothesis on the type, so `Nat.card G` is the genuine order of $G$, and the bound on the $p$-torsion is a bound on the number of elements killed by $p$, not on a rank.
--
--   This is the elementary statement that a finite abelian $p$-group whose socle has order at most $p$ is cyclic, with the order bound coming from the exponent. It is used in the formalisation wherever a finite abelian group arising as a torsion or inertia-type subquotient is to be recognised as cyclic, for instance by [`AddSubgroup.inZeroComponentAt_of_cyclic_stable_scalar_dichotomy`](thm.html#AddSubgroup.inZeroComponentAt_of_cyclic_stable_scalar_dichotomy) and [`FreyPackage.frey_no_cofixed_large`](thm.html#FreyPackage.frey_no_cofixed_large).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsAddCyclic_of_card_torsion_le_of_exponent_dvd_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsAddCyclic.of_card_torsion_le_of_exponent_dvd_pow
    {G : Type*} [AddCommGroup G] [Finite G] {p : ℕ} (hp : p.Prime) (m : ℕ)
    (hexp : ∀ x : G, p ^ m • x = 0)
    (hsocle : Nat.card {x : G // p • x = 0} ≤ p) :
    IsAddCyclic G ∧ Nat.card G ∣ p ^ m := by sorry
