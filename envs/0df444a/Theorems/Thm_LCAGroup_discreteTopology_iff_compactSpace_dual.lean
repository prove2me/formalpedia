-- Prove2me | Theorems.Thm_LCAGroup_discreteTopology_iff_compactSpace_dual
-- name    : LCAGroup.discreteTopology_iff_compactSpace_dual
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:16.44919+00:00
-- url     : https://prove2.me/theorems/22eb72fd-bf4d-477c-aa6d-051fdc773014
-- title:
--   Compact–discrete duality (Theorem D.1.1.1(2)–(3)) — a Hausdorff locally compact abelian group $G$ is discrete if and only if $\widehat G$ is compact
-- statement:
--   **Compact–discrete duality, second half.**
--
--   Let $G$ be a Hausdorff locally compact abelian group, and let $\widehat G$ be its Pontryagin dual: the group of continuous characters $\chi\colon G\to U(1)$, endowed with the compact-open topology. Then
--   $$G\ \text{is discrete}\quad\Longleftrightarrow\quad\widehat G\ \text{is compact}.$$
--
--   This is the statement dual to Theorem D.1.1.1(3) of the source ($G$ is compact if and only if $\widehat G$ is discrete; platform theorem `LCAGroup.compactSpace_iff_discreteTopology_dual`): it is obtained from it by applying Pontryagin duality $G\cong\widehat{\widehat G}$ (Theorem D.1.1.1(2)) to $\widehat G$. The source invokes it as "compact-discrete duality" in the proof of Lemma D.1.4.6(4): for an open subgroup $H\subseteq G$ the quotient $G/H$ is discrete, so $H^\perp\cong\widehat{G/H}$ is compact. The basic example is $\widehat{\mathbb Z}\cong\mathbb T$.
--
--   **Formalization Note.** $\widehat G$ is Mathlib's `PontryaginDual G` (continuous homomorphisms $G\to$ `Circle` with the compact-open topology); $G$ is written multiplicatively. The implication "discrete $\Rightarrow$ compact dual" is a Mathlib instance (`PontryaginDual.instCompactSpaceOfDiscreteTopology`); the converse, which rests on the duality theorem $G\cong\widehat{\widehat G}$, is not in Mathlib.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 746, Theorem D.1.1.1(2)–(3), and p. 758, proof of Lemma D.1.4.6 ("compact-discrete duality"); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Proposition 3.1.5 (for the implication discrete ⇒ compact dual; the converse follows from Theorem D.1.1.1(2)–(3))

import Mathlib

open Topology

set_option autoImplicit false

namespace LCAGroup

theorem discreteTopology_iff_compactSpace_dual
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    DiscreteTopology G ↔ CompactSpace (PontryaginDual G) := by sorry

end LCAGroup
