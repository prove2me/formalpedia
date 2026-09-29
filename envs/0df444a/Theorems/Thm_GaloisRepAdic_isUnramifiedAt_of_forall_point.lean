-- Prove2me | Theorems.Thm_GaloisRepAdic_isUnramifiedAt_of_forall_point
-- name    : GaloisRepAdic.isUnramifiedAt_of_forall_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/640b896d-fcb3-59bb-81b5-da8e783ebce9
-- title:
--   Unramifiedness descends along a jointly injective family of points
-- statement:
--   Let $P$ be a commutative local ring, let $\iota$ be an index type, and let $A_i$ for $i \in \iota$ be commutative local rings. Let $\chi_i \colon P \to A_i$ be ring homomorphisms, each local (non-units go to non-units), and assume the family is jointly injective: if $\chi_i(x) = 0$ for every $i$, then $x = 0$. Let $\rho$ be a [`GaloisRepAdic P`](def/GaloisRep_Adic.html#L16), that is, a finite free $P$-module $V$ with $\operatorname{rank}_P V = 2$ together with a monoid homomorphism from $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ to $\operatorname{End}_P V$ that is adically continuous in the sense that for each $n$ there is a finite subextension $L$ of $\overline{\mathbb Q}/\mathbb Q$ with $\rho(\sigma)v - v \in (\mathfrak m_P^n) \cdot V$ for all $v \in V$ and all $\sigma$ fixing $L$ pointwise. Let $q$ be a natural number, and suppose that for every $i$ the base change of $\rho$ along $\chi_i$, namely $A_i \otimes_P V$ with $\sigma$ acting by $\rho(\sigma) \otimes \mathrm{id}$, is unramified at $q$: for every valuation subring $Q$ of $\overline{\mathbb Q}$ with $q$ a non-unit of $Q$ and every $\sigma$ in the image in $\operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ of the inertia subgroup of $Q$ over $\mathbb Q$, the base-changed operator attached to $\sigma$ is the identity. Then $\rho$ itself is unramified at $q$ in the same sense: $\rho(\sigma) = 1$ for all such $Q$ and $\sigma$.
--
--   This is the descent statement for unramifiedness of a two-dimensional adically continuous Galois representation over a local ring along a family of local homomorphisms that jointly detect zero, the situation of a reduced local Hecke ring together with its points. It is used in the proof that a Hecke-ring-valued representation at Taylor–Wiles level is unramified at an auxiliary prime $q$ under a condition on the trace of Frobenius.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isUnramifiedAt_of_forall_point.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.isUnramifiedAt_of_forall_point
    {P : Type} [CommRing P] [IsLocalRing P] {ι : Type} {A : ι → Type}
    [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    (χ : ∀ i, P →+* A i) (hχ : ∀ i, IsLocalHom (χ i))
    (hinj : ∀ x, (∀ i, χ i x = 0) → x = 0)
    (ρ : GaloisRepAdic P) {q : ℕ}
    (h : ∀ i, (ρ.baseChangeAlong (χ i) (hχ i)).IsUnramifiedAt q) :
    ρ.IsUnramifiedAt q := by sorry
