-- Prove2me | Theorems.Thm_IsLocalRing_exists_jointly_injective_isLocalHom_of_isReduced
-- name    : IsLocalRing.exists_jointly_injective_isLocalHom_of_isReduced
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/bef5a69b-458f-57a9-bdf0-a9a6662a8f43
-- title:
--   Reduced noetherian local ring embeds into its minimal-prime quotients
-- statement:
--   Let $T$ be a commutative ring (in the universe of types indexed by `Type`) that is local, noetherian and reduced. The assertion is the existence of a natural number $n$, a family of types $A : \mathrm{Fin}\ n \to \mathrm{Type}$, together with commutative ring structures on each $A i$ making each $A i$ an integral domain, a local ring and a noetherian ring, and a family of ring homomorphisms $\chi_i : T \to A_i$ for $i \in \mathrm{Fin}\ n$, such that three conditions hold: each $\chi_i$ is a local homomorphism (the preimage of the maximal ideal of $A_i$ is contained in, equivalently equal to, the maximal ideal of $T$, in the form that $\chi_i$ reflects units), each $\chi_i$ is surjective as a function, and the family is jointly injective in the sense that any $x \in T$ with $\chi_i(x) = 0$ for all $i$ is zero. Note that $n$ is produced by the statement rather than prescribed, and nothing is asserted about the relation between the various $A_i$ beyond the listed properties.
--
--   This is the elementary form of the statement that a reduced noetherian local ring injects into the product of its quotients by its finitely many minimal primes, each of which is a noetherian local domain receiving a surjective local homomorphism. In the present development it provides the "points" of a reduced Hecke ring, and is cited in the verification of unramifiedness at a prime for the Galois representation attached to such a ring, where a local property is checked on each of the finitely many domain quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_jointly_injective_isLocalHom_of_isReduced.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsLocalRing.exists_jointly_injective_isLocalHom_of_isReduced
    (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsReduced T] :
    ∃ (n : ℕ) (A : Fin n → Type) (_ : ∀ i, CommRing (A i)) (_ : ∀ i, IsDomain (A i))
      (_ : ∀ i, IsLocalRing (A i)) (_ : ∀ i, IsNoetherianRing (A i)) (χ : ∀ i, T →+* A i),
      (∀ i, IsLocalHom (χ i)) ∧ (∀ i, Function.Surjective (χ i)) ∧
        (∀ x : T, (∀ i, χ i x = 0) → x = 0) := by sorry
