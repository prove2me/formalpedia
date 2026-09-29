-- Prove2me | Theorems.Thm_GlobalGaloisRep_exists_finset_forall_isUnramifiedAt_of_isOpen_ker
-- name    : GlobalGaloisRep.exists_finset_forall_isUnramifiedAt_of_isOpen_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/285a95b7-c16b-5b52-b837-f9c745f685ef
-- title:
--   Open-kernel representations of G_ℚ are almost everywhere unramified
-- statement:
--   Let $G$ be a group and let $\rho$ be a group homomorphism from the group $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ` to $G$, and assume that the underlying set of the kernel of $\rho$ is open in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ (for the Krull topology carried by that automorphism group). Then there is a finite set $S$ of natural numbers such that for every prime number $p \notin S$ the representation $\rho$ is unramified at $p$ in the sense of [`GlobalGaloisRep.IsUnramifiedAt`](def/GaloisRep_GlobalUnramifiedAt.html#L9), namely: for every valuation subring $A$ of $\overline{\mathbb{Q}}$ such that the image of $p$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$, the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$-side inertia subgroup of $A$ over $\mathbb{Q}$ — that is, the image of `A.inertiaSubgroup ℚ` under the inclusion of the decomposition subgroup of $A$ over $\mathbb{Q}$ into $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ — is contained in $\ker \rho$. No continuity or topological structure on $G$ is assumed; openness of $\ker\rho$ is the only hypothesis on $\rho$.
--
--   This is the classical finiteness statement that a Galois representation of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with open kernel (equivalently, one factoring through a finite Galois extension of $\mathbb{Q}$) is unramified outside a finite set of primes, the set of primes dividing the discriminant of the fixed field. It is used to produce auxiliary primes and to control ramification: it is cited in the construction of Taylor–Wiles primes and in the analysis of Euler factors and tame level attached to weight-one newforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GlobalGaloisRep_exists_finset_forall_isUnramifiedAt_of_isOpen_ker.lean

import Mathlib
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GlobalGaloisRep.exists_finset_forall_isUnramifiedAt_of_isOpen_ker
    {G : Type*} [Group G] (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
    (hker : IsOpen ((ρ.ker : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
      Set (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))) :
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S → GlobalGaloisRep.IsUnramifiedAt ρ p := by sorry
