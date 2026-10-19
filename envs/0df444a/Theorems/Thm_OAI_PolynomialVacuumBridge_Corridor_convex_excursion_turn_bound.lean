-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_convex_excursion_turn_bound
-- name    : OAI.PolynomialVacuumBridge.Corridor.convex_excursion_turn_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T12:06:34.384579+00:00
-- url     : https://prove2.me/theorems/bb5dace0-00f6-4129-b0c3-14d5b7e072f5
-- title:
--   Excursions in convex domains turn by at most half a revolution
-- statement:
--   A finite vertex set $D$ is admissibly convex if there are integers $\ell_k<h_k$ ($k=0,1,2$) such that $v\in D$ exactly when $\ell_k<t_k(v)<h_k$ for the three tiling coordinates $t_0=2y/\sqrt3$, $t_1=x-y/\sqrt3+\frac12$, $t_2=x+y/\sqrt3+\frac12$ of the position $(x,y)$ of $v$. The star faces of $D$ are the hexagons adjacent to some vertex of $D$; following the boundary of this face set with the star faces on the right gives the star boundary walk. Let $D$ be admissibly convex and let $(g,w)$ be an excursion of $D$: it enters $D$ from outside, is self-avoiding in $D$ and exits $D$. Then
--   $$
--   -3\le\mathrm{turnUnits}(w)\le3,
--   $$
--   i.e. its total turning angle lies in $[-\pi,\pi]$.
--
--   This winding bound is what makes the real parts of the parafermionic weights of exits uniformly positive.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/BoundaryArcs.lean#L213-L247

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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_FaceBoundary
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryCharge
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryContainment
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryArcs

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.convex_excursion_turn_bound (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (e : Germ × List Bool) (he : IsExcursion D e) :
    -3 ≤ turnUnits e.2 ∧ turnUnits e.2 ≤ 3 := by sorry
