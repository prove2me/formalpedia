-- Prove2me | Theorems.Thm_MasulloGRH_open_mapping_LF
-- name    : MasulloGRH.open_mapping_LF
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-20T21:57:32.391473+00:00
-- url     : https://prove2.me/theorems/b120bf2f-c0ad-4b9a-9120-eb5ab512d8e4
-- title:
--   Theorem C.1.5.5 — Open Mapping Theorem for LF-spaces
-- statement:
--   Let $E$ be an LF-space, i.e. a Hausdorff locally convex inductive limit of a sequence of Fréchet spaces, and let $F$ be a Hausdorff topological vector space that is the union of an increasing sequence of subspaces $F_n$, each carrying a Fréchet space topology for which the inclusion $F_n\to F$ is continuous. Let $q\colon F\to E$ be a surjective continuous linear map.
--
--   Then $q$ is open. Equivalently, the induced map $F/\ker(q)\to E$ is a topological isomorphism.
--
--   In particular every continuous linear surjection between LF-spaces is open. No strictness of the inductive limits is assumed. The draft uses this theorem to show that certain LF-spaces are strict.
--
--   **Formalization Note** The images of the maps $u_n\colon F_n\to F$ are the subspaces $F_n$ with the Fréchet topology of $F_n/\ker u_n$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.1.5, Theorem C.1.5.5 (Open Mapping Theorem), p. 665

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem open_mapping_LF (E F : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup F] [Module ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
    [ContinuousSMul ℂ F] [T2Space F] (hE : IsLF E)
    (hF : ∃ (X : ℕ → Submodule ℂ F) (τ : ∀ n, TopologicalSpace (X n)), Monotone X ∧
      (∀ x : F, ∃ n, x ∈ X n) ∧ (∀ n, @IsFrechet (X n) _ _ (τ n)) ∧
      ∀ n, @Continuous (X n) F (τ n) _ Subtype.val)
    (q : F →ₗ[ℂ] E) (hq : Continuous q) (hsurj : Function.Surjective q) :
    IsOpenMap q := by sorry

end MasulloGRH
