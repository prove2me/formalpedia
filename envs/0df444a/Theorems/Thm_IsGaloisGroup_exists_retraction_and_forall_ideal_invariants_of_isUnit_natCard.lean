-- Prove2me | Theorems.Thm_IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard
-- name    : IsGaloisGroup.exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/d406904b-87ed-51bc-840b-34bddd9d684c
-- title:
--   Reynolds retraction onto the invariants of a tame group action
-- statement:
--   Let $O$ be a noetherian commutative ring, let $A$ and $B$ be commutative rings, each an $O$-algebra, with $B$ an $A$-algebra forming a scalar tower over $O$, and suppose $B$ is an $O$-algebra of finite type. Let $G$ be a finite group acting on $B$ by ring automorphisms, the action commuting with the $O$-scalar multiplication, such that $G$ is a Galois group for $A \to B$ in the sense of Mathlib's `IsGaloisGroup` (in particular $A$ is identified, via `IsGaloisGroup.ringEquivFixedPoints`, with the fixed subring $B^G$), and such that the $A$-action on $B$ is faithful, so that $A \to B$ is injective. Assume the image of $\operatorname{card} G$ in $O$ is a unit. Then: there is an $A$-linear map $r : B \to A$ with $r(a) = a$ for every $a \in A$; for every ideal $\mathfrak a \subseteq O$, an element $a \in A$ whose image in $B$ lies in $\mathfrak a B$ already lies in $\mathfrak a A$, and every $b \in B$ with $g \cdot b - b \in \mathfrak a B$ for all $g \in G$ is congruent modulo $\mathfrak a B$ to the image of some $a \in A$; $B$ is a finite $A$-module; $A$ is an $O$-algebra of finite type; and $A$ is flat over $O$ whenever $B$ is.
--
--   This is the standard package of consequences of the Reynolds operator $b \mapsto |G|^{-1}\sum_{g} g\cdot b$ for a finite group action whose order is invertible in the base: the invariants are an $A$-linear direct summand of $B$, so that forming invariants is compatible with reduction modulo an ideal of $O$ (the two ideal clauses say exactly $\mathfrak a B \cap A = \mathfrak a A$ and $(B/\mathfrak a B)^G = A/\mathfrak a A$), together with the finiteness statements of E. Noether's theorem and the Artin–Tate lemma, which do not use invertibility of $|G|$. It is used in the construction of finitely presented smooth invariants for a Galois action with smooth fibres, via [`IsGaloisGroup.finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers`](thm.html#IsGaloisGroup.finitePresentation_and_smooth_invariants_typeZero_of_isUnit_natCard_of_smooth_fibers).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsGaloisGroup_exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsGaloisGroup.exists_retraction_and_forall_ideal_invariants_of_isUnit_natCard
    (O A B : Type) [CommRing O] [IsNoetherianRing O] [CommRing A] [CommRing B]
    [Algebra O A] [Algebra O B] [Algebra A B] [IsScalarTower O A B] [Algebra.FiniteType O B]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G O B]
    [IsGaloisGroup G A B] [FaithfulSMul A B]
    (hG : IsUnit ((Nat.card G : ℕ) : O)) :
    (∃ r : B →ₗ[A] A, ∀ a : A, r (algebraMap A B a) = a) ∧
    (∀ 𝔞 : Ideal O,
      (∀ a : A, algebraMap A B a ∈ 𝔞.map (algebraMap O B) → a ∈ 𝔞.map (algebraMap O A)) ∧
      (∀ b : B, (∀ g : G, g • b - b ∈ 𝔞.map (algebraMap O B)) →
        ∃ a : A, algebraMap A B a - b ∈ 𝔞.map (algebraMap O B))) ∧
    Module.Finite A B ∧ Algebra.FiniteType O A ∧
    (Module.Flat O B → Module.Flat O A) := by sorry
