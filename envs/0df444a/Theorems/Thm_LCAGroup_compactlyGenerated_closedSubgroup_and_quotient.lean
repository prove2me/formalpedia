-- Prove2me | Theorems.Thm_LCAGroup_compactlyGenerated_closedSubgroup_and_quotient
-- name    : LCAGroup.compactlyGenerated_closedSubgroup_and_quotient
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:23.604514+00:00
-- url     : https://prove2.me/theorems/46ea5910-e2f1-468b-b21b-553956de68c2
-- title:
--   Theorem D.1.4.3(1) — closed subgroups and Hausdorff quotients of a compactly generated locally compact abelian group are compactly generated
-- statement:
--   **Permanence of compact generation for locally compact abelian groups** (Theorem D.1.4.3(1) of the source, second assertion).
--
--   Let $G$ be a Hausdorff locally compact abelian group which is *compactly generated* (Definition D.1.4.1): some compact neighbourhood of the identity generates $G$ as a group. Let $H\subseteq G$ be a closed subgroup. Then:
--
--   1. $H$, with the subspace topology, is compactly generated;
--   2. the quotient group $G/H$ is compactly generated.
--
--   Statement 1 is special to the abelian case (a finitely generated discrete free group has closed subgroups that are not finitely generated). In the source, both statements are used in the structure theory of §D.1.4.3: the groups $A_{ij}=G_j/K_i$, quotients of open compactly generated subgroups $G_j\subseteq G$ by compact subgroups $K_i$, are compactly generated, hence elementary abelian Lie groups once they are known to be locally Euclidean.
--
--   **Formalization Note.** 'Compactly generated' (Definition D.1.4.1) is written out as `∃ U ∈ 𝓝 1, IsCompact U ∧ Subgroup.closure U = ⊤`: some compact neighbourhood of the identity generates the group. The same formula is used for the topological groups `H` (the subgroup as a type, with the subspace topology) and `G ⧸ H` (the quotient group with the quotient topology) in the conclusion. The hypothesis `hH : IsClosed (H : Set G)` is the source's assumption that $H$ is closed (so that $H$ is locally compact and $G/H$ is Hausdorff).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 757–758, Definition D.1.4.1 and Theorem D.1.4.3(1) (with the paragraph following the theorem)

import Mathlib

open Topology

set_option autoImplicit false

namespace LCAGroup

theorem compactlyGenerated_closedSubgroup_and_quotient
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (hG : ∃ U ∈ 𝓝 (1 : G), IsCompact U ∧ Subgroup.closure U = ⊤)
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    (∃ U ∈ 𝓝 (1 : H), IsCompact U ∧ Subgroup.closure U = ⊤) ∧
    (∃ U ∈ 𝓝 (1 : G ⧸ H), IsCompact U ∧ Subgroup.closure U = ⊤) := by sorry

end LCAGroup
