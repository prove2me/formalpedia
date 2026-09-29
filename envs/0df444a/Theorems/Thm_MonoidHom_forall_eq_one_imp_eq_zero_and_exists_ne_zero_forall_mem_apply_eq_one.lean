-- Prove2me | Theorems.Thm_MonoidHom_forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one
-- name    : MonoidHom.forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/0c046657-7c59-543f-bbda-2d6d39b350b8
-- title:
--   Characters separate points; proper character subgroups have non-trivial annihilator
-- statement:
--   Let $p$ be a prime, let $M$ be a finite additive abelian group all of whose elements satisfy $p \cdot m = 0$, and let $L$ be an algebraically closed field of characteristic zero. Characters of $M$ are taken to be monoid homomorphisms $\chi : \mathrm{Multiplicative}\,M \to L^{\times}$, evaluated at elements $\mathrm{Multiplicative.ofAdd}\,m$ for $m \in M$. The theorem asserts the conjunction of two statements. First, characters separate points: for every $m \in M$, if $\chi(\mathrm{ofAdd}\,m) = 1$ for every character $\chi$, then $m = 0$. Second, for every subgroup $K$ of the group of characters with $K \neq \top$, there exists $m \in M$ with $m \neq 0$ such that $\chi(\mathrm{ofAdd}\,m) = 1$ for all $\chi \in K$; that is, a proper subgroup of the character group has non-trivial annihilator in $M$.
--
--   This is the non-degeneracy of the duality pairing between a finite abelian group of exponent dividing $p$ and its group of $L^{\times}$-valued characters, in the form of Pontryagin duality for finite abelian groups. It is used in the analysis of finite flat models of residual representations, where an element of $M$ annihilated by all characters in a given subgroup produces the required non-trivial invariant line; it is cited by [`HopfAlgebra.act_eq_nsmul_of_inertiaCyclotomicChain_padicInt`](thm.html#HopfAlgebra.act_eq_nsmul_of_inertiaCyclotomicChain_padicInt) and by the two unipotent-model existence results [`ResidualGaloisRep.exists_submodule_inertia_eq_smul_and_unipotent_model_of_eq_bot`](thm.html#ResidualGaloisRep.exists_submodule_inertia_eq_smul_and_unipotent_model_of_eq_bot) and [`ResidualGaloisRep.exists_unipotent_model_of_isLocallyFlatCocycleAd_of_isLocalRing_cartierDual`](thm.html#ResidualGaloisRep.exists_unipotent_model_of_isLocallyFlatCocycleAd_of_isLocalRing_cartierDual).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MonoidHom_forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MonoidHom.forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] [Finite M] (hM : ∀ m : M, p • m = 0)
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] :
    (∀ m : M, (∀ χ : Multiplicative M →* Lˣ, χ (Multiplicative.ofAdd m) = 1) → m = 0) ∧
    (∀ K : Subgroup (Multiplicative M →* Lˣ), K ≠ ⊤ →
      ∃ m : M, m ≠ 0 ∧ ∀ χ ∈ K, χ (Multiplicative.ofAdd m) = 1) := by sorry
