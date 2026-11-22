-- Prove2me | Theorems.Thm_LCAGroup_isCompact_iff_isOpen_annihilator
-- name    : LCAGroup.isCompact_iff_isOpen_annihilator
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:22:52.707943+00:00
-- url     : https://prove2.me/theorems/fa7cbda5-90bd-4292-9fac-bf3c0172fcc8
-- title:
--   Lemma D.1.4.6(3) and Definition D.1.5.1(1) — a closed subgroup $H$ of a locally compact abelian group $G$ is compact if and only if its annihilator $H^\perp$ is open in $\widehat G$
-- statement:
--   **Annihilators of compact subgroups** (Lemma D.1.4.6(3) of the source, with its converse from Definition D.1.5.1(1)).
--
--   Let $G$ be a Hausdorff locally compact abelian group with Pontryagin dual $\widehat G$, let $H\subseteq G$ be a closed subgroup, and let
--   $$H^\perp=\{\chi\in\widehat G:\ \chi(H)=1\}\qquad\text{(D.1.4.6)}$$
--   be its annihilator, a closed subgroup of $\widehat G$. Then
--   $$H\ \text{is compact}\quad\Longleftrightarrow\quad H^\perp\ \text{is open in }\widehat G.$$
--
--   Lemma D.1.4.6(3) states the implication "$H$ compact $\Rightarrow$ $H^\perp$ open"; the converse for closed $H$ is recorded in Definition D.1.5.1(1) of the source, where a closed subgroup $k$ is called *good* if $k^\perp$ is open ("equivalent to compactness of $k$") and compactly generated. The equivalence is an instance of compact–discrete duality, via $\widehat G/H^\perp\cong\widehat H$ (Lemma D.1.4.6(2)). It is the reason why the good subgroups entering the definition of the Schwartz–Bruhat space are compact, so that one can average over them.
--
--   **Formalization Note.** $H^\perp$ is the platform definition `LCAGroup.annihilator H`, a subgroup of Mathlib's `PontryaginDual G`; compactness of $H$ and openness of $H^\perp$ are stated for the underlying sets. The hypothesis `hH : IsClosed (H : Set G)` is the standing assumption of Lemma D.1.4.6 and is needed only for the implication from right to left.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 758, Definition D.1.4.5 and Lemma D.1.4.6(3), and p. 760, Definition D.1.5.1(1); classical reference: A. Deitmar and S. Echterhoff, Principles of Harmonic Analysis, Second Edition, Springer, 2014, Proposition 3.6.1 and Proposition 3.1.5

import Mathlib
import Definitions.Def_LCAGroup_Annihilator

open Topology

set_option autoImplicit false

namespace LCAGroup

theorem isCompact_iff_isOpen_annihilator
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    IsCompact (H : Set G) ↔ IsOpen (annihilator H : Set (PontryaginDual G)) := by sorry

end LCAGroup
