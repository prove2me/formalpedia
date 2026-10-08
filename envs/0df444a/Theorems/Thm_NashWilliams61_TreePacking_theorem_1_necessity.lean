-- Prove2me | Theorems.Thm_NashWilliams61_TreePacking_theorem_1_necessity
-- name    : NashWilliams61.TreePacking.theorem_1_necessity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:50.761286+00:00
-- url     : https://prove2.me/theorems/2ce40d46-b834-4b25-8b9e-6d6cefaa9841
-- title:
--   Theorem 1, necessity — $k$ edge-disjoint spanning trees force $|E_P(G)| \ge k(|P|-1)$
-- statement:
--   Let $G$ be a finite multigraph without loops on vertex set $V$ and let $k$ be a positive integer. If $G$ has $k$ edge-disjoint spanning trees, then every partition $P$ of $V$ satisfies
--   $$|E_P(G)| \ge k\,(|P| - 1),$$
--   that is, $G$ is admissible.
--
--   This is the easy half of Theorem 1: each tree, after shrinking the members of $P$ to points, remains connected and so contributes at least $|P| - 1$ crossing edges.
--
--   **Formalization Note** The inequality is in $\mathbb Z$.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), pp. 445–446, Theorem 1, Proof of Necessity

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs
open NagamochiIbaraki.EdgeConn

namespace NashWilliams61.TreePacking

/-- **Theorem 1, Proof of Necessity** (Nash-Williams 1961, pp. 445–446). If `G` has `k`
edge-disjoint spanning trees, every partition `P` of `V(G)` satisfies (1),
`|E_P(G)| ≥ k(|P| − 1)`. -/
theorem theorem_1_necessity {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (k : ℕ) (hk : 0 < k)
    (hT : HasKTrees k ends) : IsAdmissible k ends := by sorry

end NashWilliams61.TreePacking
