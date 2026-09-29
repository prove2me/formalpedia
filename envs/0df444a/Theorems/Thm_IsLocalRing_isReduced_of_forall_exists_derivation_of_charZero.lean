-- Prove2me | Theorems.Thm_IsLocalRing_isReduced_of_forall_exists_derivation_of_charZero
-- name    : IsLocalRing.isReduced_of_forall_exists_derivation_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/c89ef189-a2ff-55e3-be99-a2e3cad132d5
-- title:
--   Derivation criterion for reducedness in characteristic zero
-- statement:
--   Let $k$ be a field of characteristic zero and let $A$ be a Noetherian local commutative ring equipped with a $k$-algebra structure. Assume two hypotheses. First, every $a \in A$ is congruent modulo the maximal ideal $\mathfrak m$ of $A$ to a scalar: there is $c \in k$ with $a - c\cdot 1 \in \mathfrak m$, i.e. the composite $k \to A \to A/\mathfrak m$ is surjective, so the residue field is $k$. Second, every $k$-linear map $\varphi : A \to k$ that vanishes on $\mathfrak m^2$ and on the image of $k$ under the structure map lifts to a derivation: there is a $k$-derivation $D : A \to A$ with $D a - \varphi(a)\cdot 1 \in \mathfrak m$ for all $a \in A$, that is, $D$ reduces modulo $\mathfrak m$ to $\varphi$. Under these assumptions the conclusion is that $A$ is reduced, i.e. its nilradical is trivial: the only nilpotent element of $A$ is $0$. Note that $k$ is taken in the lowest universe.
--
--   This is the local-algebra form of Cartier's theorem that group schemes in characteristic zero are reduced, in the formulation where tangent vectors at the closed point are assumed to extend to global derivations. It is applied in the construction of the group law on the Jacobian, to show that the local ring at the identity of the relevant scheme is reduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isReduced_of_forall_exists_derivation_of_charZero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.isReduced_of_forall_exists_derivation_of_charZero
    (k : Type) [Field k] [CharZero k] (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A]
    (hk : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A)
    (hder : ∀ φ : A →ₗ[k] k, (∀ a ∈ (IsLocalRing.maximalIdeal A) ^ 2, φ a = 0) → (∀ c : k, φ (algebraMap k A c) = 0) →
      ∃ D : Derivation k A A, ∀ a : A, D a - algebraMap k A (φ a) ∈ IsLocalRing.maximalIdeal A) :
    IsReduced A := by sorry
