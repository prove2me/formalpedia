-- Prove2me | Theorems.Thm_HenselianLocalRing_exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal
-- name    : HenselianLocalRing.exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/03bd8b19-cae2-5606-a2ad-a66a0549f789
-- title:
--   Teichmüller lift of a unit in a Henselian local ring
-- statement:
--   Let $A$ be a commutative ring which is local and Henselian (in the sense of Mathlib's `HenselianLocalRing`), and suppose its residue field $k = A/\mathfrak m$ is finite, with $q =$ `Nat.card` $k$ its cardinality. Then for every $u \in A$ that is a unit there exists $\omega \in A$ with $\omega^{q-1} = 1$ and $\omega - u \in \mathfrak m$, where $\mathfrak m$ is the maximal ideal of $A$. Note that the exponent is the natural-number difference $q - 1$, and that $\omega$ is only asserted to satisfy $\omega^{q-1}=1$ and to be congruent to $u$ modulo $\mathfrak m$; no uniqueness, and no multiplicativity in $u$, is claimed here.
--
--   This is the existence half of the classical Teichmüller section $k^\times \to \mu_{q-1}(A) \subseteq A^\times$, giving for each unit a $(q-1)$-st root of unity in its residue class. It is used in [`IsLocalRing.ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span`](thm.html#IsLocalRing.ringHom_comp_eq_of_forall_sub_mem_maximalIdeal_of_apply_eq_of_maximalIdeal_eq_span), where ring homomorphisms out of such a ring are compared by their effect on roots of unity and on a generator of the maximal ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HenselianLocalRing_exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal.lean

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.SetTheory.Cardinal.Finite

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HenselianLocalRing.exists_pow_card_residueField_sub_one_eq_one_sub_mem_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
    [Finite (IsLocalRing.ResidueField A)] {u : A} (hu : IsUnit u) :
    ∃ ω : A, ω ^ (Nat.card (IsLocalRing.ResidueField A) - 1) = 1 ∧
      ω - u ∈ IsLocalRing.maximalIdeal A := by sorry
