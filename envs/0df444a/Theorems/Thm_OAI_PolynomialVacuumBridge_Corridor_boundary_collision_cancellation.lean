-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_boundary_collision_cancellation
-- name    : OAI.PolynomialVacuumBridge.Corridor.boundary_collision_cancellation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:56:10.02183+00:00
-- url     : https://prove2.me/theorems/30d3ec40-e80d-4c18-acf8-380338c14531
-- title:
--   Collision contributions cancel in filled domains
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. Let $D$ be a filled domain (every polygon made of edges of $D$ encloses only vertices of $D$), and let $g$ be a germ entering $D$ from outside. Then the weighted sum of walks that end by colliding vanishes, even when restricted to walks through a given vertex $v$:
--   $$
--   \sum_{\substack{w\in\mathrm{leaves}(D,g)\\ \mathrm{end}(w)\in D}}\mathrm{wordWeight}(w)=0,\qquad\sum_{\substack{w\in\mathrm{leaves}(D,g)\\ \mathrm{end}(w)\in D,\ v\in w}}\mathrm{wordWeight}(w)=0 .
--   $$
--
--   Only walks that exit the domain contribute to the observable.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/CollisionCancellation.lean#L145-L170

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

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.boundary_collision_cancellation (D : Finset Vertex) (g : Germ)
    (hD : Filled D) (hg : (reverseGerm g).1 ∉ D) :
    collisionSum D g = 0 ∧ ∀ v : Vertex,
      (∑ w ∈ leaves D g, if (terminalGerm g w).1 ∈ D ∧ v ∈ traced g w
        then wordWeight w else 0) = 0 := by sorry
