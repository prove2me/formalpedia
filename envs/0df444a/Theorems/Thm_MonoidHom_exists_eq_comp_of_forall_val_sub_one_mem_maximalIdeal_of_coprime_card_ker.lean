-- Prove2me | Theorems.Thm_MonoidHom_exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker
-- name    : MonoidHom.exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/f9cbef5d-af0f-5b1d-a0ba-6b04ac728b9f
-- title:
--   Residually trivial character descends along a p'-order kernel
-- statement:
--   Let $G$ be a finite group, $\Delta$ a group, and $R$ a commutative local ring with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal R`. Let $\pi \colon G \to \Delta$ be a surjective group homomorphism, let $p$ be a natural number whose image in $R$ lies in $\mathfrak m$, and assume that the cardinality $\#\ker\pi$ (as a natural number, via `Nat.card`) is coprime to $p$. Let $\xi \colon G \to R^\times$ be a homomorphism which is residually trivial, i.e. $\xi(g) - 1 \in \mathfrak m$ for every $g \in G$, where $\xi(g)$ is regarded as an element of $R$ through the inclusion $R^\times \subseteq R$. The conclusion is that there exists a group homomorphism $\chi \colon \Delta \to R^\times$ with $\xi(g) = \chi(\pi(g))$ for all $g \in G$; that is, $\xi$ factors through $\pi$ as $\xi = \chi \circ \pi$. Note that $p$ is not assumed prime, and no topological or continuity hypotheses occur.
--
--   This is the descent step used to produce the diamond character at a Taylor–Wiles prime: a residually trivial character of $(\mathbb{Z}/q)^\times$ factors through its maximal $p$-quotient, because the kernel has order prime to $p$. It is cited by [`ValuationSubring.exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one`](thm.html#ValuationSubring.exists_inertiaCharacter_eq_comp_of_forall_cyclotomic_eq_one), where $\xi$ is an inertia character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MonoidHom_exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker.lean

import Mathlib
import Definitions.Def_Deformations_TameDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

theorem MonoidHom.exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker {G : Type u} {Δ : Type v} {R : Type w} [Group G] [Finite G] [Group Δ] [CommRing R] [IsLocalRing R]
    (π : G →* Δ) (hπ : Function.Surjective π) {p : ℕ} (hp : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hcop : (Nat.card π.ker).Coprime p)
    (ξ : G →* Rˣ) (hξ : ∀ g, (ξ g : R) - 1 ∈ IsLocalRing.maximalIdeal R) :
    ∃ χ : Δ →* Rˣ, ∀ g, ξ g = χ (π g) := by sorry
