-- Prove2me | Theorems.Thm_LeightonRao_Uniform_lp_duality
-- name    : LeightonRao.Uniform.lp_duality
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:35.462791+00:00
-- url     : https://prove2.me/theorems/26062918-2fb0-4415-bb5c-9aa5f48a425a
-- title:
--   §2.2, p. 796 — LP duality for the UMFP: optimal distance functions satisfying (5) have total weight W = f
-- statement:
--   Let $G$ be a connected network on $n\ge2$ nodes and $f$ the max-flow of its uniform multicommodity flow problem. Then
--
--   1. every distance function $d$ satisfying the distance constraint $\sum_{\{u,v\}}d(u,v)\ge1$ has total weight $W=\sum_{e}C(e)d(e)\ge f$;
--   2. some distance function $d$ satisfying the distance constraint has total weight exactly
--   $$W=f.$$
--
--   This is the linear-programming duality between the concurrent flow problem and the problem of apportioning edge lengths, which the paper cites from Chvátal (1983), Iri (1967) and Shahrokhi–Matula (1986); the proof of Theorem 2 uses it as "the fact that $W=f$".
--
--   **Formalization Note** Distances $d(u,v)$ are shortest-walk lengths in the graph of positive-capacity edges, so connectivity is assumed. The paper states this without proof; it is recorded here as the milestone on which Theorem 2 rests.
-- source:
--   Leighton and Rao, Multicommodity max-flow min-cut theorems and their use in designing approximation algorithms, J. ACM 46 (1999), p. 796, §2.2, Eqs. (4)–(5) and the sentence 'From the duality theory of linear programming ... W = f'

import Definitions.Def_LeightonRao_Uniform_Flow
import Definitions.Def_LeightonRao_Uniform_Dual

set_option autoImplicit false
open scoped BigOperators

namespace LeightonRao.Uniform

/-- The duality sentence of §2.2: every feasible distance gives an upper bound,
and an optimal one has total weight equal to the concurrent maximum flow. -/
theorem lp_duality {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hn : 2 ≤ Fintype.card V) (hconn : IsConnectedNet N) :
    (∀ d : V → V → ℝ, IsDistanceFunction d →
      SatisfiesDistanceConstraint N d → maxFlow N uniformDemand ≤ totalWeight N d) ∧
    (∃ d : V → V → ℝ, IsDistanceFunction d ∧
      SatisfiesDistanceConstraint N d ∧ totalWeight N d = maxFlow N uniformDemand) := by sorry

end LeightonRao.Uniform
