-- Prove2me | Theorems.Thm_MasulloGRH_injectiveLCLimit_weakDual_isEmbedding_and_range
-- name    : MasulloGRH.injectiveLCLimit_weakDual_isEmbedding_and_range
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:21:00.524829+00:00
-- url     : https://prove2.me/theorems/f65289c4-c091-484c-8616-e7faddb9d935
-- title:
--   Lemma C.1.6.1(1) — the weak dual of a countable locally convex inductive limit is the projective limit of the weak duals of the steps
-- statement:
--   **Topological duals of inductive limits, weak topologies (Lemma C.1.6.1(1)).** Let $(E_k)_{k\ge 0}$ be Hausdorff locally convex spaces over $\mathbb C$ with continuous linear transition maps $j_k\colon E_k\to E_{k+1}$, and let $E$ be a Hausdorff locally convex space together with continuous linear maps $i_k\colon E_k\to E$ which exhibit $E$ as the locally convex inductive limit of the system with injective maps: every $i_k$ is injective, $i_{k+1}\circ j_k=i_k$ for all $k$, $E=\bigcup_k i_k(E_k)$, and the topology of $E$ is the finest locally convex topology for which all the $i_k$ are continuous. (Then every $j_k$ is injective as well. Hausdorffness of $E$ is a hypothesis; it is automatic when the system is strict.)
--
--   For a locally convex space $F$ write $F'_\sigma$ for its topological dual with the weak topology $\sigma(F',F)$ of pointwise convergence on $F$. Consider the restriction map
--   $$q\colon E'_\sigma\longrightarrow\prod_{k\ge 0}(E_k)'_\sigma,\qquad q(\ell)=(\ell\circ i_k)_{k\ge 0},$$
--   where the target carries the product topology. Then:
--
--   1. $q$ is a topological embedding (injective, and a homeomorphism onto its image);
--   2. the image of $q$ is the projective limit of the duals,
--   $$q(E')=\varprojlim_k (E_k)'=\Bigl\{(\ell_k)_{k\ge 0}\in\prod_k (E_k)':\ \ell_{k+1}\circ j_k=\ell_k\ \text{for all }k\Bigr\}.$$
--
--   In other words $q$ is a linear homeomorphism of $E'_\sigma$ onto $\varprojlim_k (E_k)'_\sigma$, the projective limit carrying the topology induced by the product of the weak duals.
--
--   The source records this for later use: the duals of the Schwartz–Bruhat spaces and of the other inductive limits of Fréchet spaces that it studies are computed step by step through this identification.
--
--   **Formalization Note.** The inductive limit is encoded by the platform structure `RiemannMasullo.IsInjectiveLCLimit j i` (injectivity of the $i_k$, compatibility, exhaustion, and the topology of `E` equal to `RiemannMasullo.locallyConvexFinalTopology`). The source indexes the system by all pairs $m\le m'$; only the consecutive maps $j_k$ are needed. `WeakDual ℂ F` is Mathlib's dual with the weak-$*$ topology, and the projective limit is expressed as the set of compatible families inside the product `∀ k, WeakDual ℂ (X k)`; the conjunction "embedding with this range" is the statement that $q$ is a homeomorphism onto the projective limit.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 669, Lemma C.1.6.1(1) (Topological duals of inductive limits)

import Mathlib
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem injectiveLCLimit_weakDual_isEmbedding_and_range {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [T2Space E]
    [PolynormableSpace ℂ E]
    {X : ℕ → Type*} [∀ k, AddCommGroup (X k)] [∀ k, Module ℂ (X k)]
    [∀ k, TopologicalSpace (X k)] [∀ k, IsTopologicalAddGroup (X k)]
    [∀ k, ContinuousSMul ℂ (X k)] [∀ k, T2Space (X k)] [∀ k, PolynormableSpace ℂ (X k)]
    {j : ∀ k, X k →L[ℂ] X (k + 1)} {i : ∀ k, X k →L[ℂ] E}
    (h : RiemannMasullo.IsInjectiveLCLimit j i) :
    Topology.IsEmbedding (fun (L : WeakDual ℂ E) (k : ℕ) =>
        StrongDual.toWeakDual (L.toStrongDual.comp (i k))) ∧
      Set.range (fun (L : WeakDual ℂ E) (k : ℕ) =>
        StrongDual.toWeakDual (L.toStrongDual.comp (i k))) =
        {l : ∀ k, WeakDual ℂ (X k) | ∀ (k : ℕ) (x : X k), l (k + 1) (j k x) = l k x} := by sorry

end MasulloGRH
