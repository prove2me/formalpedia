-- Prove2me | Theorems.Thm_MasulloGRH_frechet_equiv_closed_subspace_bidual
-- name    : MasulloGRH.frechet_equiv_closed_subspace_bidual
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-20T23:36:16.81758+00:00
-- url     : https://prove2.me/theorems/28d6c7a3-35cb-4ec2-9800-1233535a4f13
-- title:
--   A Fréchet space embeds as a closed subspace of its strong bidual
-- statement:
--   Let $E$ be a complex Fréchet space and let $(E'_\beta)'_\beta$ be its strong bidual. There is a closed complex-linear subspace $V$ of the strong bidual and a continuous linear equivalence
--
--   $$E\cong V\subseteq (E'_\beta)'_\beta.$$
--
--   This strengthens `MasulloGRH.frechet_equiv_subspace_bidual` by requiring the image subspace to be closed. The topological embedding follows from first countability and the Hahn–Banach seminorm argument. Completeness supplies closedness: the embedding is uniform for the additive uniform structures, and a complete subspace of a Hausdorff uniform space is closed.
--
--   The result is a supporting refinement of the bidual argument for the reverse direction of the Fréchet nuclearity duality theorem, Masullo Lemma C.2.4.11, p. 689. It is stated separately from the original mission target and does not assert that $E$ equals its full bidual.
-- source:
--   Strengthening of the mission theorem https://prove2.me/theorems/d983b29e-b5c6-441b-9fb0-ed96f1a4966d (Frechet embedding in its strong bidual), supporting A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Appendix C, Lemma C.2.4.11, p. 689, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Closedness follows from the standard complete-subspace theorem for Hausdorff uniform spaces, Mathlib IsUniformEmbedding.isClosedEmbedding.

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
open MasulloGRH Topology Filter Set

theorem MasulloGRH.frechet_equiv_closed_subspace_bidual (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    ∃ V : Submodule ℂ (StrongDual ℂ (StrongDual ℂ E)),
      IsClosed (V : Set (StrongDual ℂ (StrongDual ℂ E))) ∧ Nonempty (E ≃L[ℂ] V) := by sorry
