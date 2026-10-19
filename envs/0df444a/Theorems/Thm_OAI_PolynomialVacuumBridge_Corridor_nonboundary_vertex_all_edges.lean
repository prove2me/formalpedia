-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_nonboundary_vertex_all_edges
-- name    : OAI.PolynomialVacuumBridge.Corridor.nonboundary_vertex_all_edges
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:49:11.608412+00:00
-- url     : https://prove2.me/theorems/402095cf-6a77-4131-8993-d6b0b6da55cc
-- title:
--   Cell vertices off the loop have all their edges in the cell
-- statement:
--   Let $(g,w)$ be a closed walk on the honeycomb lattice ($\mathrm{terminalGerm}(g,w)=g$), let $q=\mathrm{wordFlow}(g,w)$ be its integer edge flow, and let $p$ be a finitely supported integer face potential representing $q$: the oriented flow at every germ equals $p(\mathrm{left})-p(\mathrm{right})$. The cell of $p$ is the set of faces in the support of $p$, with its cell edges and cell vertices. If $v$ is a cell vertex of $\operatorname{supp}p$ that is not visited by the walk, then all three edges at $v$ are cell edges:
--   $$
--   \mathrm{edge}(v,k)\in\mathrm{cellEdges}(\operatorname{supp}p)\qquad(k=0,1,2).
--   $$
--
--   So away from the loop, the cell is locally complete.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/PotentialSupport.lean#L112-L128

import Mathlib
import Definitions.Def_HoneycombBridgeFiniteness
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Basic
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Excursions
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_IntegerPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_EdgeFlow
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Contours
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Cells
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RationalPotential
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Currents
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PotentialSupport

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.nonboundary_vertex_all_edges (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w))
    (v : Vertex) (hv : v ∈ cellVertices p.support) (hnot : v ∉ traced g w)
    (k : Fin 3) : edgeOf (v,k) ∈ cellEdges p.support := by sorry
