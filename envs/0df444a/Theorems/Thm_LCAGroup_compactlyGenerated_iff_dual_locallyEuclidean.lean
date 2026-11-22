-- Prove2me | Theorems.Thm_LCAGroup_compactlyGenerated_iff_dual_locallyEuclidean
-- name    : LCAGroup.compactlyGenerated_iff_dual_locallyEuclidean
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:26.764327+00:00
-- url     : https://prove2.me/theorems/99aa3e02-4ae0-49fb-ac97-864f714b3d41
-- title:
--   Theorem D.1.4.3(1) — a Hausdorff locally compact abelian group $G$ is compactly generated if and only if its dual $\widehat G$ is locally Euclidean
-- statement:
--   **Compactly generated groups are the duals of abelian Lie groups** (Theorem D.1.4.3(1) of the source, first assertion).
--
--   Let $G$ be a Hausdorff locally compact abelian group with Pontryagin dual $\widehat G$ (continuous characters $G\to U(1)$ with the compact-open topology). Recall (Definition D.1.4.1) that $G$ is *compactly generated* if there is a compact neighbourhood $U\subseteq G$ of the identity that generates $G$ as a group, and that a topological group is *locally Euclidean* if the identity (equivalently, every point) has an open neighbourhood homeomorphic to an open subset of some $\mathbb R^n$. Then
--   $$G\ \text{is compactly generated}\quad\Longleftrightarrow\quad\widehat G\ \text{is locally Euclidean}.$$
--
--   Under Pontryagin duality a compactly generated group $\mathbb R^a\times\mathbb Z^b\times K$ ($K$ compact) corresponds to the Lie group $\mathbb R^a\times\mathbb T^b\times\widehat K$ ($\widehat K$ discrete). The source uses this equivalence to write every Hausdorff locally compact abelian group as an inverse limit of locally Euclidean groups (Lemma D.1.4.4), and in the notion of a good subgroup $k\subseteq G$ (Definition D.1.5.1: $k^\perp$ open and compactly generated), which makes the quotients $\Gamma/k$ elementary abelian Lie groups.
--
--   **Formalization Note.** 'Compactly generated' (Definition D.1.4.1) is written out as `∃ U ∈ 𝓝 1, IsCompact U ∧ Subgroup.closure U = ⊤`: some compact neighbourhood of the identity generates the group. 'Locally Euclidean' is expressed without a new definition: there are $n$ and an `OpenPartialHomeomorph` (a homeomorphism between an open subset of the group and an open subset of `EuclideanSpace ℝ (Fin n)`) whose source contains the identity. For a topological group this is equivalent, by translation, to every point having a neighbourhood homeomorphic to an open subset of $\mathbb R^n$. $\widehat G$ is Mathlib's `PontryaginDual G`; groups are written multiplicatively.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 757, Definition D.1.4.1 and Theorem D.1.4.3(1); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Corollaries 4.2.5 and 4.2.6

import Mathlib

open Topology

set_option autoImplicit false

namespace LCAGroup

theorem compactlyGenerated_iff_dual_locallyEuclidean
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    (∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = ⊤) ↔
      ∃ (n : ℕ) (e : OpenPartialHomeomorph (PontryaginDual G) (EuclideanSpace ℝ (Fin n))),
        (1 : PontryaginDual G) ∈ e.source := by sorry

end LCAGroup
