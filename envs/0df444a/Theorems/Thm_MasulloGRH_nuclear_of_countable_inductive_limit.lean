-- Prove2me | Theorems.Thm_MasulloGRH_nuclear_of_countable_inductive_limit
-- name    : MasulloGRH.nuclear_of_countable_inductive_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-20T22:04:49.212405+00:00
-- url     : https://prove2.me/theorems/1e09b521-8e39-450c-b069-96a797ed86bb
-- title:
--   Lemma C.2.4.12(1) — a Hausdorff inductive limit of a sequence of nuclear spaces is nuclear
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$ which is the locally convex inductive limit of a sequence $E_0\to E_1\to\cdots$ of nuclear Hausdorff locally convex spaces with injective continuous transition maps: $E$ is the union of the $E_n$ and carries the finest locally convex topology for which all the maps $E_n\to E$ are continuous. Then $E$ is nuclear.
--
--   This is the permanence property by which LF-spaces built from nuclear Fréchet spaces are nuclear.
--
--   **Formalization Note** The steps are subspaces $E_n\subset E$, each with its own nuclear topology. Part (2) of the source, on projective limits, is not included.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.2.4.4, Lemma C.2.4.12 (Nuclearity of inductive and projective limits), part (1), p. 689

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem nuclear_of_countable_inductive_limit (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E) (X : ℕ → Submodule ℂ E)
    (τ : ∀ n, TopologicalSpace (X n)) (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (hmono : ∀ n, ∃ h : X n ≤ X (n + 1),
      @Continuous (X n) (X (n + 1)) (τ n) (τ (n + 1)) (Submodule.inclusion h))
    (hnuc : ∀ n, @IsNuclear (X n) _ _ (τ n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E (τ n) t Subtype.val}) :
    IsNuclear E := by sorry

end MasulloGRH
