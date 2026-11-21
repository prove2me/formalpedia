-- Prove2me | Theorems.Thm_MasulloGRH_bounded_in_strict_frechet_stages
-- name    : MasulloGRH.bounded_in_strict_frechet_stages
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:45:24.7937+00:00
-- url     : https://prove2.me/theorems/8ce2cf63-1b22-4823-a38c-ccc1a5d6e175
-- title:
--   Localization of bounded sets for an induced Fréchet exhaustion
-- statement:
--   For an increasing exhaustive sequence of Fréchet subspaces with the induced topologies and the stated final locally convex topology, the ambient space is Hausdorff locally convex and every bounded set is the image of a bounded set in one stage. Unlike the general strict-limit boundedness proposition, stage closedness need not be supplied here: it follows from completeness.
-- source:
--   Masullo, The Music of the Primes, frozen 20 November 2026 draft, proof of Corollary C.1.5.13, pp. 668–669, using Proposition C.1.5.3, Lemma C.1.5.4 and Example C.1.5.10. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_LocallyConvex

namespace MasulloGRH

theorem bounded_in_strict_frechet_stages (E : Type*) [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E]
    (X : ℕ → Submodule ℂ E) (hmono : Monotone X) (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (hX : ∀ n, IsFrechet (X n)) (htop : t = sInf {τ | IsLocallyConvexTopology E τ ∧
      ∀ n, @Continuous (X n) E _ τ Subtype.val}) :
    IsHLCS E ∧ ∀ B : Set E, Bornology.IsVonNBounded ℂ B → ∃ (n : ℕ) (A : Set (X n)),
      Bornology.IsVonNBounded ℂ A ∧ B = Subtype.val '' A := by sorry

end MasulloGRH
