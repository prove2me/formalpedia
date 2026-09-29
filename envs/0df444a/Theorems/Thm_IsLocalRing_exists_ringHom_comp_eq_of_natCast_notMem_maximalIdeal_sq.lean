-- Prove2me | Theorems.Thm_IsLocalRing_exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq
-- name    : IsLocalRing.exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/781a3760-e659-5441-9500-0deb58e162d1
-- title:
--   Lifting a residue embedding into a square-zero thickening
-- statement:
--   Let $q$ be a prime number. Let $S$ be a commutative local ring whose residue field is finite of characteristic $q$, and suppose that the image of $q$ under the canonical map $\mathbb{N} \to S$ does not lie in $\mathfrak{m}_S^2$, the square of the maximal ideal of $S$. Let $D$ be a commutative local ring whose maximal ideal satisfies $\mathfrak{m}_D^2 = \bot$, i.e. is square-zero, let $K$ be a field, and let $\pi_D : D \to K$ be a surjective ring homomorphism (so that $K$ is identified with the residue field of $D$). Finally, let $x : S \to K$ be a ring homomorphism whose kernel is exactly $\mathfrak{m}_S$, that is, an embedding of the residue field of $S$ into $K$. The conclusion is that $x$ lifts through $\pi_D$: there exists a ring homomorphism $\psi : S \to D$ such that $\psi$ followed by $\pi_D$ equals $x$. No flatness, completeness or noetherian hypothesis on $S$ is imposed, and $\psi$ is asserted to exist but is not claimed to be unique.
--
--   This is the lifting property of local rings that are unramified at $q$ in the weak sense that $q \notin \mathfrak{m}_S^2$, in the spirit of the Cohen-type structure theory for local rings with finite residue field: such an $S$ admits a map to any square-zero thickening of a field receiving its residue field. It is used in the verification that the rings arising in a prorepresentability statement for the relevant deformation functor have regular local stalks with $q$ nonzero, via [`AlgebraicGeometry.isRegularLocalRing_stalk_and_natCast_ne_zero_of_isProrepresentedBy`](thm.html#AlgebraicGeometry.isRegularLocalRing_stalk_and_natCast_ne_zero_of_isProrepresentedBy).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open IsLocalRing

theorem IsLocalRing.exists_ringHom_comp_eq_of_natCast_notMem_maximalIdeal_sq
    {q : ℕ} [Fact q.Prime] {S : Type u} [CommRing S] [IsLocalRing S]
    [Finite (ResidueField S)] [CharP (ResidueField S) q]
    (hq : ((q : ℕ) : S) ∉ maximalIdeal S ^ 2)
    {D : Type v} [CommRing D] [IsLocalRing D] (hD : maximalIdeal D ^ 2 = ⊥)
    {K : Type w} [Field K] (πD : D →+* K) (hπD : Function.Surjective πD)
    (x : S →+* K) (hx : RingHom.ker x = maximalIdeal S) :
    ∃ ψ : S →+* D, πD.comp ψ = x := by sorry
