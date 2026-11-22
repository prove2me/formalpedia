-- Prove2me | Theorems.Thm_MasulloGRH_injectiveLCLimit_isEmbedding_of_strict
-- name    : MasulloGRH.injectiveLCLimit_isEmbedding_of_strict
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:47.768852+00:00
-- url     : https://prove2.me/theorems/4ae5ce6f-38b8-4d5d-81a9-727c55c14782
-- title:
--   Strict countable locally convex inductive limits: the canonical maps $E_k\to\varinjlim E_k$ are topological embeddings, and the limit is Hausdorff if the steps are
-- statement:
--   **Strict inductive limits, in terms of transition maps.** Let $(E_k)_{k\ge 0}$ be locally convex spaces over $\mathbb C$ with continuous linear transition maps $j_k\colon E_k\to E_{k+1}$, and let $E$ be the locally convex inductive limit of the system, with canonical maps $i_k\colon E_k\to E$: every $i_k$ is injective, $i_{k+1}\circ j_k=i_k$, $E=\bigcup_k i_k(E_k)$, and $E$ carries the finest locally convex topology for which all the $i_k$ are continuous. Assume the system is *strict*: every $j_k$ is a topological embedding. Then:
--
--   1. every canonical map $i_k\colon E_k\to E$ is a topological embedding;
--   2. if every $E_k$ is Hausdorff, then $E$ is Hausdorff.
--
--   This is the theorem of Dieudonné and Schwartz on strict inductive limits, in the form in which the source quotes it: for a strict system "automatically such an inductive limit $E$ is Hausdorff and each $E_k\to E$ is a topological embedding". It is what makes Lemma C.1.6.1 and the theory of strict LF-spaces applicable to limits given by abstract stage data.
--
--   **Formalization Note.** The inductive limit is encoded by the platform structure `RiemannMasullo.IsInjectiveLCLimit j i`. Local convexity of the steps is Mathlib's `PolynormableSpace ℂ (X k)` (the topology is defined by the family of all continuous seminorms). No Hausdorff hypothesis is needed for part 1.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 662, Example C.1.4.6(4), and p. 664 (paragraph before Definition C.1.5.2); classical reference: H. H. Schaefer with M. P. Wolff, Topological Vector Spaces, Second Edition, Springer, Ch. II, 6.4 (as cited by the paper)

import Mathlib
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem injectiveLCLimit_isEmbedding_of_strict {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E]
    {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
    [∀ k, TopologicalSpace (X k)] [∀ k, IsTopologicalAddGroup (X k)]
    [∀ k, PolynormableSpace ℂ (X k)]
    {j : ∀ k, X k →L[ℂ] X (k + 1)} {i : ∀ k, X k →L[ℂ] E}
    (h : RiemannMasullo.IsInjectiveLCLimit j i) (hj : ∀ k, Topology.IsEmbedding (j k)) :
    (∀ k, Topology.IsEmbedding (i k)) ∧ ((∀ k, T2Space (X k)) → T2Space E) := by sorry

end MasulloGRH
