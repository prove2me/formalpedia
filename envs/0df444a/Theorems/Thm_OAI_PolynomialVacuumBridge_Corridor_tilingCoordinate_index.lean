-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_tilingCoordinate_index
-- name    : OAI.PolynomialVacuumBridge.Corridor.tilingCoordinate_index
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:59:21.762252+00:00
-- url     : https://prove2.me/theorems/c844913f-0453-4a3c-be69-386cb35795b8
-- title:
--   Tiling coordinates are box indices plus a fractional offset
-- statement:
--   Place $\mathrm{up}(i,j)$ at $\bigl(i+\frac j2,\ (j+\frac13)\frac{\sqrt3}2\bigr)$ and $\mathrm{down}(i,j)$ at $\bigl(i+\frac j2+\frac12,\ (j+\frac23)\frac{\sqrt3}2\bigr)$. The three tiling coordinates of a point $(x,y)$ are $t_0=2y/\sqrt3$, $t_1=x-y/\sqrt3+\frac12$ and $t_2=x+y/\sqrt3+\frac12$. For every vertex $v$ and direction $k$ there is $a\in(0,1)$ with
--   $$
--   t_k(\mathrm{position}(v))=\mathrm{boxIndex}_k(v)+a,
--   $$
--   where the box indices are $(j,i,i+j)$ for $\mathrm{up}(i,j)$ and $(j,i,i+j+1)$ for $\mathrm{down}(i,j)$.
--
--   So no vertex lies on an integer tiling line.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Convexity.lean#L17-L47

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

theorem OAI.PolynomialVacuumBridge.Corridor.tilingCoordinate_index (v : Vertex) (k : Fin 3) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧
      tilingCoordinate k (position v) = (boxIndex v k : ℝ) + a := by sorry
