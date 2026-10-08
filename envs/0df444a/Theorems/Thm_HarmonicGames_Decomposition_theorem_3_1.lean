-- Prove2me | Theorems.Thm_HarmonicGames_Decomposition_theorem_3_1
-- name    : HarmonicGames.Decomposition.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:52:20.85915+00:00
-- url     : https://prove2.me/theorems/9e204ee9-5aba-4fc8-85c6-ecd1efae9627
-- title:
--   Theorem 3.1 — Helmholtz decomposition: $C_1 = \operatorname{im}\delta_0 \oplus \ker\Delta_1 \oplus \operatorname{im}\delta_1^*$
-- statement:
--   Let $G = (E, A)$ be a finite undirected graph, $C_1$ its space of edge flows with $\langle X, Y\rangle_1 = \frac12\sum_{(p,q)\in A} X(p,q)Y(p,q)$, $\delta_0$ the combinatorial gradient, $\delta_1$ the curl, $\delta_0^*$, $\delta_1^*$ their adjoints and $\Delta_1 = \delta_1^*\delta_1 + \delta_0\delta_0^*$ the vector Laplacian.
--
--   **Theorem 3.1 (Helmholtz Decomposition).** The vector space of edge flows admits an orthogonal decomposition
--
--   $$
--   C_1 = \operatorname{im}(\delta_0) \oplus \ker(\Delta_1) \oplus \operatorname{im}(\delta_1^*),
--   $$
--
--   where $\ker(\Delta_1) = \ker(\delta_1) \cap \ker(\delta_0^*)$.
--
--   The three summands are the globally consistent flows (gradients), the harmonic flows (locally but not globally consistent) and the locally inconsistent flows. Pulled back through the map $D$ that sends a game to its flow of pairwise comparisons, this decomposition gives the potential–harmonic–nonstrategic decomposition of games (Theorem 4.1).
--
--   **Formalization Note** "Orthogonal decomposition" is stated as: the three subspaces are pairwise orthogonal (`Submodule.IsOrtho`) and their sum is all of $C_1$; pairwise orthogonality makes the sum direct. The graph is an arbitrary finite simple graph.
-- source:
--   Candogan, Menache, Ozdaglar, Parrilo, Flows and Decompositions of Games: Harmonic and Potential Games, arXiv:1005.2405v2, p. 11, Theorem 3.1, eq. (17)

import Mathlib
import Definitions.Def_HarmonicGames_Decomposition_Flows

namespace HarmonicGames.Decomposition

theorem theorem_3_1 {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    (LinearMap.range (delta0 G)).IsOrtho (LinearMap.ker (Delta1 G)) ∧
    (LinearMap.range (delta0 G)).IsOrtho (LinearMap.range (LinearMap.adjoint (delta1 G))) ∧
    (LinearMap.ker (Delta1 G)).IsOrtho (LinearMap.range (LinearMap.adjoint (delta1 G))) ∧
    LinearMap.range (delta0 G) ⊔ LinearMap.ker (Delta1 G) ⊔
        LinearMap.range (LinearMap.adjoint (delta1 G)) = ⊤ ∧
    LinearMap.ker (Delta1 G) =
      LinearMap.ker (delta1 G) ⊓ LinearMap.ker (LinearMap.adjoint (delta0 G)) := by sorry

end HarmonicGames.Decomposition
