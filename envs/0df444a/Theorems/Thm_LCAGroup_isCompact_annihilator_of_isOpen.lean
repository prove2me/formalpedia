-- Prove2me | Theorems.Thm_LCAGroup_isCompact_annihilator_of_isOpen
-- name    : LCAGroup.isCompact_annihilator_of_isOpen
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:36.985687+00:00
-- url     : https://prove2.me/theorems/28fb6ee9-540e-4717-a8db-47c930237c10
-- title:
--   Lemma D.1.4.6(4) — the annihilator $H^\perp\subseteq\widehat G$ of an open subgroup $H$ of a locally compact abelian group $G$ is compact
-- statement:
--   **Annihilators of open subgroups** (Lemma D.1.4.6(4) of the source).
--
--   Let $G$ be a Hausdorff locally compact abelian group with Pontryagin dual $\widehat G$, and let $H\subseteq G$ be an open subgroup (hence also closed). Then its annihilator
--   $$H^\perp=\{\chi\in\widehat G:\ \chi(H)=1\}\qquad\text{(D.1.4.6)}$$
--   is a compact subgroup of $\widehat G$.
--
--   This is an instance of compact–discrete duality: $G/H$ is discrete and $H^\perp\cong\widehat{G/H}$ (Lemma D.1.4.6(2)). In the source it is applied (with the roles of $G$ and $\widehat G$ exchanged by Pontryagin duality) to the open compactly generated subgroups of $\widehat G$: the kernels $K_i$ of (D.1.4.10) are annihilators of such subgroups and are therefore compact, which is used in §D.1.4.3 to form the quotients $A_{ij}=G_j/K_i$.
--
--   **Formalization Note.** $H^\perp$ is the platform definition `LCAGroup.annihilator H`, a subgroup of Mathlib's `PontryaginDual G`; openness of $H$ and compactness of $H^\perp$ are stated for the underlying sets. No closedness hypothesis is needed, since open subgroups of a topological group are closed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 758, Definition D.1.4.5 and Lemma D.1.4.6(4); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Proposition 3.6.1 and Proposition 3.1.5

import Mathlib
import Definitions.Def_LCAGroup_Annihilator

open Topology

set_option autoImplicit false

namespace LCAGroup

theorem isCompact_annihilator_of_isOpen
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    IsCompact (annihilator H : Set (PontryaginDual G)) := by sorry

end LCAGroup
