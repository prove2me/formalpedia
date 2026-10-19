-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_Polygon_trace_left_potential
-- name    : OAI.PolynomialVacuumBridge.Corridor.Polygon.trace_left_potential
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:55:32.52976+00:00
-- url     : https://prove2.me/theorems/7271f430-dff4-4678-8f97-4287cba3a447
-- title:
--   The polygon potential is constant along walks avoiding the polygon
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. Let $P$ be a polygon (the edge set of a simple closed walk) with its indicator potential $p_P$, which is $\pm1$ on the enclosed faces and $0$ elsewhere. If a walk $(g,w)$ visits no vertex of $P$, then the potential of its left face does not change:
--   $$
--   p_P\bigl(\mathrm{leftFace}(\mathrm{terminalGerm}(g,w))\bigr)=p_P\bigl(\mathrm{leftFace}(g)\bigr).
--   $$
--
--   A walk that does not touch a polygon cannot cross from its outside to its inside.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/PolygonGeometry.lean#L246-L260

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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Polygons
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionPhase
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CycleSplice
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionHistories
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_PolygonGeometry

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor OAI.PolynomialVacuumBridge.Corridor.Polygon

theorem OAI.PolynomialVacuumBridge.Corridor.Polygon.trace_left_potential (P : Polygon) (g : Germ) (w : List Bool)
    (hdis : ∀ v ∈ traced g w, v ∉ P.vertices) :
    P.potential (leftFace (terminalGerm g w)) = P.potential (leftFace g) := by sorry
