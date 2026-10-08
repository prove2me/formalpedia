-- Prove2me | Theorems.Thm_LeightonRao_Uniform_theorem_2
-- name    : LeightonRao.Uniform.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:50.808353+00:00
-- url     : https://prove2.me/theorems/ead20ec4-3bee-456c-9caf-28096266eb90
-- title:
--   Theorem 2, p. 795 — for every uniform multicommodity flow problem, Ω(𝒮/log n) ≤ f ≤ 𝒮
-- statement:
--   For a network on $n$ nodes, let $f$ be the max-flow and $\mathcal S$ the min-cut of its uniform multicommodity flow problem (demand one between every pair of nodes). There is an absolute constant $c>0$ such that for every connected network on $n\ge2$ nodes
--   $$c\,\frac{\mathcal S}{\log n}\le f\le\mathcal S .$$
--
--   This is the approximate max-flow min-cut theorem for uniform demands: the min-cut can exceed the max-flow by at most a logarithmic factor, and the example of §2.1 (Theorem 1) shows the factor $\Theta(\log n)$ is attained.
--
--   **Formalization Note** $\Omega(\mathcal S/\log n)$ is rendered with one constant $c$ chosen before the network, uniform over all vertex types and capacities. The proof in the paper gives $c=1/36$. $\log n=\log_2n$ (footnote 3). Connectivity is the paper's standing assumption (p. 789) and $n\ge2$ is needed for a cut to exist. Uniform demands are two ordered commodities of demand $\tfrac12$ per pair (footnote 2).
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 795, Theorem 2

import Definitions.Def_LeightonRao_Uniform_Flow

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- Theorem 2, p. 795. The Ω constant is independent of the network and its size. -/
theorem theorem_2 :
    ∃ c : ℝ, 0 < c ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (N : Network V),
        2 ≤ Fintype.card V → IsConnectedNet N →
          c * minCut N / Real.logb 2 (Fintype.card V : ℝ) ≤
            maxFlow N uniformDemand ∧
          maxFlow N uniformDemand ≤ minCut N := by sorry

end LeightonRao.Uniform
