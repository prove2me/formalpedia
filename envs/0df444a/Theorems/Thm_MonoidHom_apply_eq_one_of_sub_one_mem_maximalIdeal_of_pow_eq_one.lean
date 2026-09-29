-- Prove2me | Theorems.Thm_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one
-- name    : MonoidHom.apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/990cb349-9fde-5e9f-9785-2975d8fb01c7
-- title:
--   Characters trivial mod 𝔪 vanish on invertible-order elements
-- statement:
--   Let $G$ be a group and $A$ a commutative local ring with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal A`. Let $\chi \colon G \to A^\times$ be a monoid homomorphism (a character of $G$ with values in the units of $A$), and let $g \in G$. Assume that the image of $\chi(g)$ in $A$ is congruent to $1$ modulo $\mathfrak m$, i.e. $\chi(g) - 1 \in \mathfrak m$, and that there is a natural number $n$ whose image in $A$ is a unit and for which $g^n = 1$. The conclusion is that $\chi(g) = 1$ in $A^\times$. No finiteness of $G$ and no condition on the order of $g$ beyond the existence of such an $n$ is required; in particular $n$ need not be the exact order of $g$.
--
--   This is the statement that a character into the group $1 + \mathfrak m$ of one-units of a local ring is trivial on elements of order invertible in $A$; equivalently, there are no nontrivial homomorphisms from a prime-to-$p$ torsion group into $1 + \mathfrak m_A$ when $p$ is the residue characteristic. It is used at Taylor–Wiles primes, where the diagonal character must be shown to kill the prime-to-$p$ part of inertia, and it feeds into [`MonoidHom.exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker`](thm.html#MonoidHom.exists_eq_comp_of_forall_val_sub_one_mem_maximalIdeal_of_coprime_card_ker), which factors such a character through a quotient.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u w

open IsLocalRing

theorem MonoidHom.apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one {G : Type u} {A : Type w} [Group G] [CommRing A] [IsLocalRing A]
    (χ : G →* Aˣ) (g : G) (hprin : (χ g : A) - 1 ∈ IsLocalRing.maximalIdeal A)
    {n : ℕ} (hn : IsUnit (n : A)) (hgn : g ^ n = 1) : χ g = 1 := by sorry
