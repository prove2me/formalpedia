-- Prove2me | Theorems.Thm_OAI_Release075_MarkedLineData_x_turn_large
-- name    : OAI.Release075.MarkedLineData.x_turn_large
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:08:32.506378+00:00
-- url     : https://prove2.me/theorems/cd60d8f9-5356-4dcf-a6c3-713bfbc0a7bb
-- title:
--   Turning between two different x-edges of one label is long
-- statement:
--   For marked-line data $d$ with parameter $r>0$, the link graph is the disjoint union of the complete bipartite graph on the $l$- and $r$-edges at $o$ and the shift-scheme links at $v$ and $w$. A direction at $o$ has weight $3$ and directions at $v,w$ have weight $1$. Let $i$ be a label and $(u,v)\ne(u',v')$. Consider a reduced walk $p$ in the link from the direction of the reversed oriented edge $x_{i,u',v'}$ to the direction of the oriented edge $x_{i,u,v}$ at their common vertex. Then
--   $$
--   5\le\mathrm{weight}\cdot\mathrm{length}(p).
--   $$
--
--   This bounds the boundary turn between consecutive $x$-edges with the same label.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Links.lean#L114-L137

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links

open OAI OAI.Release075 OAI.Release075.MarkedLineData
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem OAI.Release075.MarkedLineData.x_turn_large (i : d.Label) (u v u' v' : Fin r) (s t : Bool)
    (ht : (d.presentation hr).edgeTarget ((d.presentation hr).flipEdge (.inl (i,u',v'),t)) =
      (d.presentation hr).edgeTarget (.inl (i,u,v),s))
    (hne : (u,v) ≠ (u',v'))
    (p : (d.allLink hr).Walk
      (d.linkDirection hr ((d.presentation hr).flipEdge (.inl (i,u',v'),t)))
      (d.linkDirection hr (.inl (i,u,v),s)))
    (hp : ReducedWalk p) :
    5 ≤ TriangleRibbon.weight (d.linkColor hr (d.linkDirection hr (.inl (i,u,v),s))) * p.length := by sorry
