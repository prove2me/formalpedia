-- Prove2me | Theorems.Thm_MasulloGRH_limit_subspace_hull_condition
-- name    : MasulloGRH.limit_subspace_hull_condition
-- status  : Proved
-- author  : @Ismael Correa
-- created : 2026-11-20T23:55:33.390177+00:00
-- url     : https://prove2.me/theorems/58b0ac99-5951-448c-89dd-6744b7eec612
-- title:
--   A limit subspace of a strict LF-space satisfies the hull condition
-- statement:
--   Let $E=\bigcup_k E_k$ be a strict countable locally convex inductive limit of nuclear Fréchet spaces $E_0\subseteq E_1\subseteq\cdots$ (each $E_k$ with the topology induced by $E$, and $E$ with the finest locally convex topology making all inclusions $E_k\hookrightarrow E$ continuous). Let $F\subseteq E$ be a closed subspace which is a **limit subspace**, i.e. the topology induced on $F$ by $E$ equals the locally convex inductive limit topology of the subspaces $F\cap E_k$.
--
--   For a set $S$ write $\Gamma(S)=\operatorname{conv}_{\mathbb R}(\operatorname{bal}_{\mathbb C}S)$ for its absolutely convex hull. Then for every sequence $(W_k)$ of $0$-neighbourhoods $W_k\subseteq E_k$ there is a sequence $(O_k)$ of $0$-neighbourhoods $O_k\subseteq E_k$ such that
--   $$F\cap\Gamma\Big(\bigcup_k O_k\Big)\subseteq\Gamma\Big(\bigcup_k (W_k\cap F)\Big).$$
--
--   This is the concrete, seminorm-free form of the limit-subspace hypothesis: $\Gamma(\bigcup_k (W_k\cap F))$ is a $0$-neighbourhood of the inductive limit topology of $(F\cap E_k)$, hence of the induced topology, so it contains $F\cap O$ for an absolutely convex $0$-neighbourhood $O$ of $E$; take $O_k=O\cap E_k$.
-- source:
--   A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Appendix C, Definition C.1.5.8 and Theorem C.1.5.11 (pp. 667-669); V. S. Retakh, Subspaces of a countable inductive limit, Soviet Math. Dokl. 11 (1970); J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996).

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

theorem limit_subspace_hull_condition (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hlim : (instTopologicalSpaceSubtype : TopologicalSpace V) =
        sInf {t | IsLocallyConvexTopology V t ∧
          ∀ n, @Continuous ↥(V ⊓ X n) V _ t (Submodule.inclusion inf_le_left)}) :
    ∀ W : ∀ k, Set (X k), (∀ k, W k ∈ nhds (0 : X k)) →
      ∃ O : ∀ k, Set (X k), (∀ k, O k ∈ nhds (0 : X k)) ∧
        ∀ v ∈ V, v ∈ convexHull ℝ (balancedHull ℂ (⋃ k, Subtype.val '' O k)) →
          v ∈ convexHull ℝ (balancedHull ℂ (⋃ k, (Subtype.val '' W k) ∩ (V : Set E))) := by sorry

end MasulloGRH
