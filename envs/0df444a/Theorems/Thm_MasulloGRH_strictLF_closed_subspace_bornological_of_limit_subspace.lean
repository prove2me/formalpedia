-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_closed_subspace_bornological_of_limit_subspace
-- name    : MasulloGRH.strictLF_closed_subspace_bornological_of_limit_subspace
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:55:33.799331+00:00
-- url     : https://prove2.me/theorems/b9908fa4-8d9e-46d4-9487-aeef4dcd25de
-- title:
--   A closed limit subspace of a strict LF-space is bornological
-- statement:
--   Let $E$ be a strict countable locally convex inductive limit of Fréchet spaces: $E=\bigcup_m E_m$ for an increasing sequence of subspaces $E_0\subseteq E_1\subseteq\cdots$, each a Fréchet space for the topology induced by $E$, and $E$ carries the finest locally convex topology for which all inclusions $E_m\hookrightarrow E$ are continuous. Let $F\subseteq E$ be a closed linear subspace and assume that $F$ is a **limit subspace**: the topology induced on $F$ by $E$ coincides with the finest locally convex topology on $F$ for which all inclusions $F\cap E_m\hookrightarrow F$ are continuous.
--
--   Then $F$ is **bornological**: every seminorm on $F$ that is bounded on the bounded subsets of $F$ is continuous.
--
--   Indeed, each $F\cap E_m$ is a closed subspace of the Fréchet space $E_m$, hence metrizable and therefore bornological; a seminorm $p$ on $F$ bounded on bounded sets is bounded on the bounded subsets of every $F\cap E_m$, hence continuous on each $F\cap E_m$, so the locally convex topology defined by $p$ makes all inclusions $F\cap E_m\hookrightarrow F$ continuous and is therefore coarser than the inductive limit topology, which by hypothesis is the topology of $F$. (Countable locally convex inductive limits of metrizable spaces are bornological.)
--
--   **Formalization note.** The limit-subspace condition is written exactly as in `MasulloGRH.limit_subspace_of_bounded_lifting`; `IsBornological` is the predicate of `Definitions.Def_MasulloGRH_LocallyConvex`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Theorem C.1.5.11 (pp. 667-668), last step of (2)⇒(1); H. H. Schaefer, Topological Vector Spaces, II.8.1–8.2 (metrizable spaces and locally convex inductive limits of bornological spaces are bornological)

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_closed_subspace_bornological_of_limit_subspace
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlim : (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}) :
    IsBornological V := by sorry

end MasulloGRH
