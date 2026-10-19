-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_box_two_faces
-- name    : OAI.PolynomialVacuumBridge.Corridor.box_two_faces
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T12:01:04.829252+00:00
-- url     : https://prove2.me/theorems/0ee85873-5db6-4d92-8a6e-3090b663c0bf
-- title:
--   Box membership of an edge from two opposite faces
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. A box is given by integer bounds $\ell_k\le\mathrm{boxIndex}_k<h_k$ in the three directions. Let $v$ be a vertex, $k$ a slot, and consider the edge from $v$ through slot $k+1$. Let $r$ be a vertex of the right face of the germ $(v,k)$ and $s$ a vertex of the left face of $(\mathrm{neighbor}(v,k+1),k+2)$, two faces on opposite sides of this edge. If $r$ and $s$ both lie in the box, then
--   $$
--   v\in\text{box}\quad\text{or}\quad\mathrm{neighbor}(v,k+1)\in\text{box}.
--   $$
--
--   So a box containing vertices on both sides of an edge contains an endpoint of that edge.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Convexity.lean#L191-L206

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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionCancellation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Traversals
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ReturnCycles
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionStems
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_CollisionGrouping
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Convexity

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.box_two_faces (lo hi : Fin 3 → ℤ) (v r s : Vertex) (k : Fin 3)
    (hr : r ∈ faceVertices (rightFace (v,k)))
    (hs : s ∈ faceVertices (leftFace (neighbor v (k+1),k+2)))
    (hr' : BoxMem lo hi r) (hs' : BoxMem lo hi s) :
    BoxMem lo hi v ∨ BoxMem lo hi (neighbor v (k+1)) := by sorry
