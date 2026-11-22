-- Prove2me | Theorems.Thm_MasulloGRH_directSum_normed_exists_rescale_nhds
-- name    : MasulloGRH.directSum_normed_exists_rescale_nhds
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:20:59.453673+00:00
-- url     : https://prove2.me/theorems/d7340fbd-8f31-49db-91ec-367fa3cf119c
-- title:
--   Proposition C.1.5.1 — in a countable locally convex direct sum of normed spaces, countably many $0$-neighbourhoods can be rescaled to contain a common $0$-neighbourhood
-- statement:
--   **Rescaling countably many neighbourhoods in a countable direct sum of normed spaces (Proposition C.1.5.1).** Let $E_0,E_1,E_2,\dots$ be normed vector spaces over $\mathbb C$ and let
--   $$E=\bigoplus_{k\ge 0}E_k$$
--   be their algebraic direct sum with the locally convex direct sum topology, i.e. the finest locally convex topology for which all canonical injections $E_k\to E$ are continuous. Then for every sequence $V_0,V_1,V_2,\dots$ of neighbourhoods of $0$ in $E$ there are real numbers $\rho_i>0$ such that
--   $$\bigcap_{i\ge 0}\rho_iV_i$$
--   is a neighbourhood of $0$ in $E$.
--
--   A single normed space has this property because its $0$-neighbourhoods can be rescaled to contain the unit ball; the proposition says that the property survives countable locally convex direct sums. The source uses it to study how countable locally convex inductive limits of normable spaces interact with the projective tensor product topology (Proposition C.2.3.10).
--
--   **Formalization Note.** The direct sum is Mathlib's `⨁ k, Y k` (`DirectSum`), topologized by `RiemannMasullo.locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Y)`, the topology defined by all seminorms whose restrictions to the summands are continuous; this is the locally convex direct sum topology. The summands and the neighbourhoods are both indexed by $\mathbb N$ starting at $0$ (the source starts at $1$), and $\rho_iV_i$ is the pointwise scalar multiple `(ρ i : ℂ) • V i`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 664, Proposition C.1.5.1

import Mathlib
import Definitions.Def_RiemannMasullo_AppC_InductiveLimits

open Topology
open scoped Pointwise DirectSum

set_option autoImplicit false

namespace MasulloGRH

theorem directSum_normed_exists_rescale_nhds (Y : ℕ → Type*) [∀ k, NormedAddCommGroup (Y k)]
    [∀ k, NormedSpace ℂ (Y k)] :
    letI := RiemannMasullo.locallyConvexFinalTopology (DirectSum.lof ℂ ℕ Y)
    ∀ V : ℕ → Set (⨁ k, Y k), (∀ k, V k ∈ 𝓝 0) →
      ∃ ρ : ℕ → ℝ, (∀ k, 0 < ρ k) ∧ (⋂ k, (ρ k : ℂ) • V k) ∈ 𝓝 0 := by sorry

end MasulloGRH
