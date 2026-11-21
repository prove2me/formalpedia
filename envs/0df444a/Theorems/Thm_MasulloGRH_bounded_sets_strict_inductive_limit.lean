-- Prove2me | Theorems.Thm_MasulloGRH_bounded_sets_strict_inductive_limit
-- name    : MasulloGRH.bounded_sets_strict_inductive_limit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-20T21:49:30.529392+00:00
-- url     : https://prove2.me/theorems/9a220dc7-1a88-475e-ae46-d839ebece5d7
-- title:
--   Proposition C.1.5.3 — bounded subsets of a strict inductive limit lie and are bounded in one step
-- statement:
--   Let $E$ be a Hausdorff locally convex space over $\mathbb C$ which is the strict locally convex inductive limit of an increasing sequence of subspaces $E_0\subset E_1\subset\cdots$: $E=\bigcup_kE_k$, each $E_k$ carries the topology induced by $E$ and is closed, and $E$ carries the finest locally convex topology for which all inclusions $E_k\to E$ are continuous.
--
--   Then a subset $B\subset E$ is bounded in $E$ if and only if there is an index $k$ such that $B\subset E_k$ and $B$ is bounded in $E_k$.
--
--   This is the regularity of strict inductive limits. The draft uses it to reduce statements about bounded sets of Schwartz–Bruhat functions and $\theta$-functions to a single Fréchet step.
--
--   **Formalization Note** In a strict inductive limit each step carries the topology induced by the limit and, the transition maps being closed embeddings, is closed in the limit; the hypotheses are stated in this form.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.1.5, Proposition C.1.5.3, pp. 664–665

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem bounded_sets_strict_inductive_limit (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E) (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hcl : ∀ n, IsClosed (X n : Set E))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (B : Set E) :
    Bornology.IsVonNBounded ℂ B ↔
      ∃ (n : ℕ) (B' : Set (X n)), Bornology.IsVonNBounded ℂ B' ∧ B = Subtype.val '' B' := by sorry

end MasulloGRH
