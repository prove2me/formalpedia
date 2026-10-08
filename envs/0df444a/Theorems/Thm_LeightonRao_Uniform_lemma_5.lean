-- Prove2me | Theorems.Thm_LeightonRao_Uniform_lemma_5
-- name    : LeightonRao.Uniform.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:26:54.87244+00:00
-- url     : https://prove2.me/theorems/728fd699-8ba3-48b6-ad56-68e8ac9e6d91
-- title:
--   Lemma 5, p. 799 — |T| ≥ 2n/3 and Σ_{u∉T} d(T, u) ≥ 1/2n give a cut of ratio cost ≤ 6W
-- statement:
--   Let $G$ be a connected network on $n\ge2$ nodes and $d$ a distance function with total weight $W$. Suppose $T\subseteq V$ satisfies $|T|\ge 2n/3$ and
--   $$\sum_{u\in V\setminus T}d(T,u)\ge\frac1{2n},$$
--   where $d(T,u)=\min_{t\in T}d(t,u)$ is the shortest-path distance from $T$. Then there is a nonempty proper subset $U\subset V$ with
--   $$\frac{C(U,\bar U)}{|U|\,|\bar U|}\le 6W .$$
--
--   This handles the case of Corollary 4 in which a large component of small radius exists.
--
--   **Formalization Note** The page states the conclusion as "ratio cost $O(W)$"; the constant $6$ is the one computed in the proof on p. 800 ($R\le6W$). Connectivity is the paper's standing assumption (p. 789) and makes the graph distances well defined; $n\ge2$ makes $T$ nonempty and a proper cut exist.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 799, Lemma 5 (constant 6 from its proof, p. 800)

import Definitions.Def_LeightonRao_Uniform_Dual

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- Lemma 5, p. 799, with the proof's explicit factor `6`. -/
theorem lemma_5 {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N)
    (d : V → V → ℝ) (hd : IsDistanceFunction d)
    (T : Finset V) (hT : 2 * (Fintype.card V : ℝ) ≤ 3 * (T.card : ℝ))
    (hsum : 1 / (2 * (Fintype.card V : ℝ)) ≤ ∑ u ∈ Tᶜ, distFrom N d T u) :
    ∃ U : Finset V, U.Nonempty ∧ Uᶜ.Nonempty ∧
      ratioCost N U ≤ 6 * totalWeight N d := by sorry

end LeightonRao.Uniform
