-- Prove2me | Theorems.Thm_OAI_Release075_MarkedLineData_allLink_closed
-- name    : OAI.Release075.MarkedLineData.allLink_closed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T08:07:44.107978+00:00
-- url     : https://prove2.me/theorems/1c19dde7-9e68-45a1-aa1e-8e35f9b176eb
-- title:
--   Reduced closed link walks are long
-- statement:
--   For marked-line data $d$ with parameter $r>0$, the link graph is the disjoint union of the complete bipartite graph on the $l$- and $r$-edges at $o$ and the shift-scheme links at $v$ and $w$. A direction at $o$ has weight $3$ and directions at $v,w$ have weight $1$. Every nonempty reduced closed walk $p$ in the link graph, based at a direction $a$, satisfies
--   $$
--   12\le\mathrm{weight}(a)\cdot\mathrm{length}(p).
--   $$
--
--   So every interior vertex of a reduced diagram has angle at least $12$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/Links.lean#L55-L79

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
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem OAI.Release075.MarkedLineData.allLink_closed (a : d.AllDirections hr) (p : (d.allLink hr).Walk a a)
    (hn : 0 < p.length) (hp : ReducedWalk p) :
    12 ≤ TriangleRibbon.weight (d.linkColor hr a) * p.length := by sorry
