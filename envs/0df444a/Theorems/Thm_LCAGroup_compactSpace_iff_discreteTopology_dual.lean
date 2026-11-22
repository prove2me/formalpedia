-- Prove2me | Theorems.Thm_LCAGroup_compactSpace_iff_discreteTopology_dual
-- name    : LCAGroup.compactSpace_iff_discreteTopology_dual
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:18.225386+00:00
-- url     : https://prove2.me/theorems/4fcb3593-3160-41e7-aec6-c825bf36a8b7
-- title:
--   Theorem D.1.1.1(3) — a Hausdorff locally compact abelian group $G$ is compact if and only if its Pontryagin dual $\widehat G$ is discrete
-- statement:
--   **Compact–discrete duality, first half** (Theorem D.1.1.1(3) of the source).
--
--   Let $G$ be a Hausdorff locally compact abelian group, and let $\widehat G$ be its Pontryagin dual: the group of continuous characters $\chi\colon G\to U(1)$, endowed with the compact-open topology. Then
--   $$G\ \text{is compact}\quad\Longleftrightarrow\quad\widehat G\ \text{is discrete}.$$
--
--   Together with its companion ($G$ is discrete if and only if $\widehat G$ is compact, the platform theorem `LCAGroup.discreteTopology_iff_compactSpace_dual`) this is the basic dictionary of Pontryagin duality. In the source it is what turns statements about compact subgroups into statements about open subgroups of the dual: it is used for the annihilators of compact and of open subgroups (Lemma D.1.4.6(3)–(4)) and hence for the good subgroups and structural pairs (Definition D.1.5.1) from which the Schwartz–Bruhat space $\mathcal S(G)$ is built.
--
--   **Formalization Note.** $\widehat G$ is Mathlib's `PontryaginDual G` (continuous homomorphisms $G\to$ `Circle` with the compact-open topology); $G$ is written multiplicatively. The implication "compact $\Rightarrow$ discrete dual" is a Mathlib instance; the converse, which rests on the duality theorem $G\cong\widehat{\widehat G}$, is not in Mathlib.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 746, Theorem D.1.1.1(3); classical reference: W. Rudin, Fourier Analysis on Groups, Wiley-Interscience, 1962, 1.7.3(a)

import Mathlib

open Topology

set_option autoImplicit false

namespace LCAGroup

theorem compactSpace_iff_discreteTopology_dual
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    CompactSpace G ↔ DiscreteTopology (PontryaginDual G) := by sorry

end LCAGroup
