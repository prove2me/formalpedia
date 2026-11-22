-- Prove2me | Theorems.Thm_MasulloGRH_injectiveLCLimit_strongDual_isEmbedding_and_range
-- name    : MasulloGRH.injectiveLCLimit_strongDual_isEmbedding_and_range
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:58.044146+00:00
-- url     : https://prove2.me/theorems/a81ba4f2-2021-4b85-a79f-2800ea20a72d
-- title:
--   Lemma C.1.6.1(2) — the strong dual of a regular countable locally convex inductive limit is the projective limit of the strong duals of the steps
-- statement:
--   **Topological duals of inductive limits, strong topologies (Lemma C.1.6.1(2)).** Let $(E_k)_{k\ge 0}$ be Hausdorff locally convex spaces over $\mathbb C$ with continuous linear transition maps $j_k\colon E_k\to E_{k+1}$, and let $E$ be a Hausdorff locally convex space together with continuous linear maps $i_k\colon E_k\to E$ which exhibit $E$ as the locally convex inductive limit of the system with injective maps: every $i_k$ is injective, $i_{k+1}\circ j_k=i_k$ for all $k$, $E=\bigcup_k i_k(E_k)$, and the topology of $E$ is the finest locally convex topology for which all the $i_k$ are continuous. (Then every $j_k$ is injective as well. Hausdorffness of $E$ is a hypothesis; it is automatic when the system is strict.)
--
--   Assume in addition that every bounded subset of $E$ comes from a bounded subset of one step: for every bounded $B\subset E$ there are an index $k$ and a bounded subset $A\subset E_k$ with $B\subset i_k(A)$.
--
--   For a locally convex space $F$ write $F'_\beta$ for its strong dual, i.e. the topological dual with the topology $\beta(F',F)$ of uniform convergence on the bounded subsets of $F$. Consider the restriction map
--   $$q\colon E'_\beta\longrightarrow\prod_{k\ge 0}(E_k)'_\beta,\qquad q(\ell)=(\ell\circ i_k)_{k\ge 0},$$
--   where the target carries the product topology. Then:
--
--   1. $q$ is a topological embedding;
--   2. the image of $q$ is the projective limit
--   $$q(E')=\varprojlim_k (E_k)'=\Bigl\{(\ell_k)_{k\ge 0}\in\prod_k (E_k)':\ \ell_{k+1}\circ j_k=\ell_k\ \text{for all }k\Bigr\}.$$
--
--   In other words $q$ is a linear homeomorphism of the strong dual $E'_\beta$ onto $\varprojlim_k (E_k)'_\beta$.
--
--   The hypothesis on bounded sets holds whenever the system is strict and every $E_k\to E_{k+1}$ is a closed embedding, for instance for strict inductive limits of complete spaces (Proposition C.1.5.3 of the source). The source uses the lemma to identify the strong duals of its strict inductive limits of nuclear Fréchet spaces, such as spaces of tempered distributions on adelic groups.
--
--   **Formalization Note.** The inductive limit is encoded by `RiemannMasullo.IsInjectiveLCLimit j i`. `StrongDual ℂ F` is Mathlib's space of continuous linear functionals with the topology of uniform convergence on von Neumann bounded sets. The source's hypothesis "$B\subset E_m$ and $B$ is bounded in $E_m$" is written as $B\subset i_k(A)$ with $A$ bounded in $E_k$, which is equivalent because $i_k$ is injective and subsets of bounded sets are bounded. Statement 2 does not depend on the hypothesis on bounded sets; it is included so that the theorem states the full identification with the projective limit.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 669, Lemma C.1.6.1(2) (Topological duals of inductive limits)

import Mathlib
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem injectiveLCLimit_strongDual_isEmbedding_and_range {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [PolynormableSpace ℂ E]
    {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
    [∀ k, TopologicalSpace (X k)] [∀ k, IsTopologicalAddGroup (X k)]
    [∀ k, ContinuousSMul ℂ (X k)] [∀ k, T2Space (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    {j : ∀ k, X k →L[ℂ] X (k + 1)} {i : ∀ k, X k →L[ℂ] E}
    (h : RiemannMasullo.IsInjectiveLCLimit j i)
    (hreg : ∀ B : Set E, Bornology.IsVonNBounded ℂ B →
      ∃ (k : ℕ) (A : Set (X k)), Bornology.IsVonNBounded ℂ A ∧ B ⊆ i k '' A) :
    Topology.IsEmbedding (fun (L : StrongDual ℂ E) (k : ℕ) => L.comp (i k)) ∧
      Set.range (fun (L : StrongDual ℂ E) (k : ℕ) => L.comp (i k)) =
        {l : ∀ k, StrongDual ℂ (X k) | ∀ k : ℕ, (l (k + 1)).comp (j k) = l k} := by sorry

end MasulloGRH
