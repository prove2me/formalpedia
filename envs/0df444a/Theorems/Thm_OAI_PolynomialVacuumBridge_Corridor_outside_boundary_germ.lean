-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_outside_boundary_germ
-- name    : OAI.PolynomialVacuumBridge.Corridor.outside_boundary_germ
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T12:01:46.384468+00:00
-- url     : https://prove2.me/theorems/6f44f226-d8da-4514-9ee8-8b1d1ab078aa
-- title:
--   Vertices next to a convex domain lie on its star boundary
-- statement:
--   A finite vertex set $D$ is admissibly convex if there are integers $\ell_k<h_k$ ($k=0,1,2$) such that $v\in D$ exactly when $\ell_k<t_k(v)<h_k$ for the three tiling coordinates $t_0=2y/\sqrt3$, $t_1=x-y/\sqrt3+\frac12$, $t_2=x+y/\sqrt3+\frac12$ of the position $(x,y)$ of $v$. The star faces of $D$ are the hexagons adjacent to some vertex of $D$; following the boundary of this face set with the star faces on the right gives the star boundary walk. Let $D$ be admissibly convex, $v\notin D$ and $\mathrm{neighbor}(v,k)\in D$. Then the germ $(v,k+1)$ is on the boundary of the star faces of $D$, and the star boundary walk turns right there:
--   $$
--   (v,k+1)\in\partial\,\mathrm{starFaces}(D),\qquad\mathrm{turn}_{\mathrm{starFaces}(D)}(v,k+1)=\text{right}.
--   $$
--
--   The outside neighbours of a convex domain are exactly where the boundary walk turns towards the domain.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/BoundaryCharge.lean#L20-L36

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

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.outside_boundary_germ (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (v : Vertex) (k : Fin 3) (hv : v ∉ D) (hn : neighbor v k ∈ D) :
    OnFaceBoundary (starFaces D) (v,k+1) ∧
      faceBoundaryTurn (starFaces D) (v,k+1) = false := by sorry
