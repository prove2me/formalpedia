-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_of_projective_topology
-- name    : MasulloGRH.nuclear_of_projective_topology
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:38:24.033269+00:00
-- url     : https://prove2.me/theorems/00907815-a92b-4b47-876e-c70350e38f65
-- title:
--   Lemma C.2.4.12(2) — projective limits of nuclear spaces are nuclear
-- statement:
--   Let $(Y_i)_{i\in I}$ be a family of nuclear Hausdorff locally convex spaces over $\mathbb C$, indexed by an arbitrary set $I$, and let $E$ be a complex vector space with linear maps $\pi_i\colon E\to Y_i$. Suppose that
--
--   1. $E$ carries the **projective (initial) topology** of the family $(\pi_i)$: the coarsest topology for which every $\pi_i$ is continuous;
--   2. the maps $\pi_i$ **separate points**: if $\pi_i(x)=0$ for all $i$, then $x=0$.
--
--   Then $E$ is nuclear.
--
--   This contains part (2) of Lemma C.2.4.12 of the draft: *a Hausdorff locally convex space which is a projective limit, indexed by an arbitrary co-filtered set, of nuclear Hausdorff locally convex spaces is nuclear.* Indeed, a projective limit $E=\varprojlim Y_i$ is the space of compatible threads in $\prod_iY_i$ with the topology induced by the product; this is the initial topology of the canonical projections $\pi_i\colon E\to Y_i$, and the projections separate the points of $E$. The transition maps of the system play no role in the conclusion, so they do not appear in the statement.
--
--   **Formalization Note** Condition 1 is stated as an equality of topologies: the topology of $E$ is the infimum over $i$ of the topologies induced by the $\pi_i$. Condition 2 is equivalent to $E$ being Hausdorff, given condition 1 and that each $Y_i$ is Hausdorff. Nuclearity is `MasulloGRH.IsNuclear` (Definition C.2.4.1 of the draft).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Lemma C.2.4.12 part (2), p. 689 (the draft cites Schaefer, Topological Vector Spaces, Ch. III, 7.4)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem nuclear_of_projective_topology (ι : Type u) (Y : ι → Type u)
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] [∀ i, TopologicalSpace (Y i)]
    (hY : ∀ i, IsNuclear (Y i))
    (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (π : ∀ i, E →ₗ[ℂ] Y i)
    (htop : ‹TopologicalSpace E› = ⨅ i, TopologicalSpace.induced (π i) inferInstance)
    (hsep : ∀ x : E, (∀ i, π i x = 0) → x = 0) :
    IsNuclear E := by sorry

end MasulloGRH
