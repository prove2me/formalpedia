-- Prove2me | Theorems.Thm_MasulloGRH_limit_subspace_iff_bounded_lifting
-- name    : MasulloGRH.limit_subspace_iff_bounded_lifting
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-20T21:57:55.629998+00:00
-- url     : https://prove2.me/theorems/f73f4b98-f92a-45ea-8e92-0caeae62b230
-- title:
--   Theorem C.1.5.11 — a closed subspace of a strict inductive limit of nuclear Fréchet spaces is a limit subspace iff the quotient map lifts bounded sets
-- statement:
--   Let $E$ be a strict locally convex inductive limit of an increasing sequence $E_0\subset E_1\subset\cdots$ of nuclear Fréchet spaces, and let $F\subset E$ be a closed linear subspace. The following are equivalent:
--
--   1. $F$ is a **limit subspace**: the topology induced on $F$ by $E$ is the locally convex inductive limit topology of the subspaces $F\cap E_m$, each with the topology induced by $E_m$;
--   2. the quotient map $q\colon E\to E/F$ has the **bounded lifting property**: every bounded subset of $E/F$ is contained in $q(B')$ for some bounded subset $B'\subset E$.
--
--   Closed subspaces of strict LF-spaces need not be LF-spaces for the induced topology. The theorem gives the criterion by which the draft shows that kernels of its $\theta$-function operators are again strict inductive limits of nuclear Fréchet spaces.
--
--   **Formalization Note** The defining sequence is given: an increasing exhaustive sequence of subspaces $E_m$ of $E$, each a nuclear Fréchet space for the induced topology, with $E$ carrying the finest locally convex topology for which the inclusions $E_m\to E$ are continuous.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, §C.1.5, Theorem C.1.5.11 (Recognizing limit subspaces of strict LF-spaces), p. 668; limit subspaces: Definition C.1.5.6, p. 666; bounded lifting: Definition C.1.5.9, p. 667

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem limit_subspace_iff_bounded_lifting (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) :
    ((instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}) ↔
      LiftsBoundedSets (V.mkQ : E → E ⧸ V) := by sorry

end MasulloGRH
