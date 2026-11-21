-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_limit_subspace_of_bornological
-- name    : MasulloGRH.strictLF_limit_subspace_of_bornological
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:44:01.037487+00:00
-- url     : https://prove2.me/theorems/16d414f2-97e0-4e44-a5db-ddeedd118959
-- title:
--   A bornological closed subspace of a strict LF-space is a limit subspace
-- statement:
--   Let $E$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces: $E=\bigcup_m E_m$ for an increasing sequence of subspaces $E_0\subseteq E_1\subseteq\cdots$, each a nuclear Fréchet space for the topology induced by $E$, and $E$ carries the finest locally convex topology for which all inclusions $E_m\hookrightarrow E$ are continuous. Let $F\subseteq E$ be a closed linear subspace, $q\colon E\to E/F$ the quotient map, and for each $m$ let $P_m=E_m/(F\cap E_m)$ with the quotient topology of $E_m$, together with the natural continuous linear injection $\iota_m\colon P_m\to E/F$.
--
--   Assume $F$, with the topology induced by $E$, is **bornological**: every seminorm on $F$ that is bounded on the bounded subsets of $F$ is continuous. Then $F$ is a **limit subspace**: the topology induced on $F$ by $E$ equals the locally convex inductive limit topology of the subspaces $F\cap E_m$, each with the topology induced from $E$.
--
--   Proof idea: the subspace topology is locally convex and makes all inclusions $F\cap E_m\hookrightarrow F$ continuous, so it is coarser than the inductive limit topology. Conversely, let $t$ be a locally convex topology on $F$, given by seminorms $p_i$, for which all inclusions $F\cap E_m\hookrightarrow (F,t)$ are continuous. A bounded subset of $F$ is bounded in $E$, hence contained in some $E_m$ (bounded sets of strict LF-spaces are localized), hence bounded in $F\cap E_m$ and therefore $t$-bounded. Thus every $p_i$ is bounded on bounded sets, so continuous by bornologicity, i.e. the subspace topology is finer than $t$.
--
--   **Formalization Note** The step $P_m$ is the Lean quotient `X m ⧸ V.comap (X m).subtype` and $\iota_m$ is `Submodule.mapQ (V.comap (X m).subtype) V (X m).subtype le_rfl`; boundedness is von Neumann boundedness; `IsBornological` is the predicate of `Definitions.Def_MasulloGRH_LocallyConvex` (every seminorm bounded on bounded sets is continuous). The limit-subspace condition is written exactly as in `MasulloGRH.limit_subspace_iff_bounded_lifting`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Theorem C.1.5.11 (pp. 667-668); J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), §3, Cor. 3.4, p. 254

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem strictLF_limit_subspace_of_bornological
    (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hborn : IsBornological V) :
    (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)} := by sorry

end MasulloGRH
