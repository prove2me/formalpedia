-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_nonboundary_cellCurvature
-- name    : OAI.PolynomialVacuumBridge.Corridor.nonboundary_cellCurvature
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:52:35.920667+00:00
-- url     : https://prove2.me/theorems/4de23ff4-6493-49db-b7ee-138f6490983f
-- title:
--   Discrete curvature vanishes at cell vertices off the loop
-- statement:
--   Let $(g,w)$ be a closed walk on the honeycomb lattice ($\mathrm{terminalGerm}(g,w)=g$), let $q=\mathrm{wordFlow}(g,w)$ be its integer edge flow, and let $p$ be a finitely supported integer face potential representing $q$: the oriented flow at every germ equals $p(\mathrm{left})-p(\mathrm{right})$. The cell of $p$ is the set of faces in the support of $p$, with its cell edges and cell vertices. For a set $S$ of faces, the cell curvature at a vertex $v$ is $\kappa_S(v)=6-3\,\mathrm{edgeCount}_S(v)+\mathrm{faceCount}_S(v)$. If $v$ is a cell vertex of $\operatorname{supp}p$ not visited by the walk, then
--   $$
--   \kappa_{\operatorname{supp}p}(v)=0 .
--   $$
--
--   All curvature of the cell is concentrated on the loop.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Curvature.lean#L193-L210

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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Incidence
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Curvature

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.nonboundary_cellCurvature (g : Germ) (w : List Bool)
    (hc : terminalGerm g w = g) (p : FaceIndex →₀ ℤ)
    (hp : RepresentsFlow p (wordFlow g w)) (v : Vertex)
    (hv : v ∈ cellVertices p.support) (hnot : v ∉ traced g w) :
    cellCurvature p.support v = 0 := by sorry
