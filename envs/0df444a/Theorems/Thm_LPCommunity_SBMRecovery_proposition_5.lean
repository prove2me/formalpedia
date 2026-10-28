-- Prove2me | Theorems.Thm_LPCommunity_SBMRecovery_proposition_5
-- name    : LPCommunity.SBMRecovery.proposition_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:03:22.113649+00:00
-- url     : https://prove2.me/theorems/c409b6dc-b02f-40ce-8993-2bdc768f9929
-- title:
--   Proposition 5, p. 20 — b-factor criterion for bipartite graphs (Schrijver, Corollary 21.4a)
-- statement:
--   Let $G=(V,E)$ be a finite bipartite graph and $b\in\mathbb Z_{\ge0}^V$. Then $G$ has a $b$-factor if and only if, for each $U\subseteq V$,
--   $$
--   N(U,U)\ \ge\ b(U)-\tfrac12\,b(V),
--   $$
--   where $N(U,U)$ is the number of edges with both endpoints in $U$ and $b(U)=\sum_{v\in U}b_v$.
--
--   This is Corollary 21.4a of Schrijver's *Combinatorial Optimization*. In the paper it turns "the random bipartite graph lies in a $d$-regular bipartite graph" into a family of edge-count inequalities, one per $U$, that can be checked by concentration bounds (proof of Proposition 3).
--
--   **Formalization Note** Bipartiteness is the existence of a set $A$ such that every edge has exactly one endpoint in $A$. The inequality is compared in $\mathbb R$, since $b(V)/2$ may be a half-integer.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 20, Proposition 5 (Corollary 21.4a in Schrijver, Combinatorial Optimization)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Factors

open Finset Filter Topology
open scoped Classical

namespace LPCommunity.SBMRecovery

/-- Proposition 5 (p. 20; Schrijver, Corollary 21.4a): a bipartite graph has a `b`-factor iff
`N(U, U) ≥ b(U) − b(V)/2` for every `U ⊆ V`. -/
theorem proposition_5 {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hbip : ∃ A : Finset V, ∀ u v, G.Adj u v → (u ∈ A ↔ v ∉ A)) (b : V → ℕ) :
    HasFactor G b ↔
      ∀ U : Finset V, (edgeCount G U U : ℝ) ≥ (∑ v ∈ U, (b v : ℝ)) - (∑ v, (b v : ℝ)) / 2 := by sorry

end LPCommunity.SBMRecovery
