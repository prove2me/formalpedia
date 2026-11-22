-- Prove2me | Theorems.Thm_LCAGroup_continuousMonoidHom_dual_equiv
-- name    : LCAGroup.continuousMonoidHom_dual_equiv
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:57.173374+00:00
-- url     : https://prove2.me/theorems/63a9bffd-6495-40d8-b3bd-fd0f7f617e20
-- title:
--   Lemma D.1.6.4, corrected — duality of homomorphism groups: $\mathrm{Hom}(A,G)\cong\mathrm{Hom}(\widehat G,\widehat A)$, $f\mapsto\widehat f$, as topological groups (compact-open topologies)
-- statement:
--   **Pontryagin duality for groups of continuous homomorphisms** (Lemma D.1.6.4 and the general fact stated in its proof).
--
--   Let $A$ and $G$ be Hausdorff locally compact abelian groups with Pontryagin duals $\widehat A$, $\widehat G$. Let $\mathrm{Hom}_{\mathrm{cont}}(A,G)$ be the group of continuous homomorphisms $A\to G$ with pointwise multiplication and the compact-open topology. Every $f\in\mathrm{Hom}_{\mathrm{cont}}(A,G)$ has a dual homomorphism
--   $$\widehat f\colon\widehat G\to\widehat A,\qquad\widehat f(\chi)=\chi\circ f .$$
--
--   **Statement.** The map
--   $$\mathrm{Hom}_{\mathrm{cont}}(A,G)\longrightarrow\mathrm{Hom}_{\mathrm{cont}}(\widehat G,\widehat A),\qquad f\longmapsto\widehat f,$$
--   is an isomorphism of topological groups: a bijective group homomorphism which is a homeomorphism for the compact-open topologies.
--
--   For $A=\mathbb R$ this is Lemma D.1.6.4 of the source: the group $\mathcal L(G)=\mathrm{Hom}_{\mathrm{cont}}(\mathbb R,G)$ of one-parameter subgroups of $G$ (the "topological Lie algebra" of $G$, Definition D.1.6.1) is identified, as a topological group, with $\mathrm{Hom}_{\mathrm{cont}}(\widehat G,\widehat{\mathbb R})\cong\mathrm{Hom}_{\mathrm{cont}}(\widehat G,\mathbb R)$, the group of real characters of $\widehat G$. This identification underlies the symbol $p(\partial_a)$ of the first-order differential operator $\partial_a$ attached to $a\in\mathcal L(G)$ (Lemma D.1.6.14).
--
--   **Deviation from the source.** Lemma D.1.6.4 also asserts that $\mathrm{Hom}_{\mathrm{cont}}(\widehat G,\widehat{\mathbb R})$ is locally compact. This is false in general (for $G=\mathbb T^{\mathbb N}$ the space of one-parameter subgroups is $\mathbb R^{\mathbb N}$ with the product topology) and is not asserted here. The statement is given for a general source group $A$, as in the proof of the lemma, where the direction of the dual map is misprinted as $\mathrm{Hom}(\widehat{G_1},\widehat{G_2})$.
--
--   **Formalization Note.** `A →ₜ* G` is Mathlib's `ContinuousMonoidHom A G` with its compact-open topology and pointwise group structure, and $\widehat f$ is `PontryaginDual.map f`. The statement asserts the existence of a `ContinuousMulEquiv` `e : (A →ₜ* G) ≃ₜ* (PontryaginDual G →ₜ* PontryaginDual A)` with `e f = PontryaginDual.map f`. Mathlib has the continuous homomorphism `PontryaginDual.mapHom` but not its bijectivity or the continuity of its inverse.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 766, Lemma D.1.6.4 and its proof

import Mathlib

open Topology

set_option autoImplicit false

namespace LCAGroup

theorem continuousMonoidHom_dual_equiv
    (A G : Type*) [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]
    [T2Space A] [LocallyCompactSpace A]
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    ∃ e : (A →ₜ* G) ≃ₜ* (PontryaginDual G →ₜ* PontryaginDual A),
      ∀ f : A →ₜ* G, e f = PontryaginDual.map f := by sorry

end LCAGroup
