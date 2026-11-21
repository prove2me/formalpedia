-- Prove2me | Theorems.Thm_MasulloGRH_escaping_set_seminorm
-- name    : MasulloGRH.escaping_set_seminorm
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:28:56.076922+00:00
-- url     : https://prove2.me/theorems/bdbc1c32-8217-409c-9bd7-969aa7c7e262
-- title:
--   A seminorm detecting escape from closed stages
-- statement:
--   Let a Hausdorff locally convex space be exhausted by an increasing sequence of closed vector subspaces. If a set escapes every stage, there exists a seminorm continuous on every stage and unbounded on the set. The inductive-limit topology is not needed for this construction. The seminorm can be obtained from scaled separating functionals whose tails vanish on each fixed stage.
-- source:
--   Auxiliary separation argument for Masullo, The Music of the Primes, frozen 20 November 2026 draft, Proposition C.1.5.3, pp. 664–665. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloGRH_LocallyConvex

namespace MasulloGRH

theorem escaping_set_seminorm (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (hE : IsHLCS E)
    (X : ℕ → Submodule ℂ E) (hmono : Monotone X) (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (hcl : ∀ n, IsClosed (X n : Set E)) (B : Set E)
    (hesc : ∀ n, ∃ x ∈ B, x ∉ X n) :
    ∃ p : Seminorm ℂ E, (∀ n, Continuous (fun x : X n => p (x : E))) ∧ ¬ BddAbove (p '' B) := by sorry

end MasulloGRH
