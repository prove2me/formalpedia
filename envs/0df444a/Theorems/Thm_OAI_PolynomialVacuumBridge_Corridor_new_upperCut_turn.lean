-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_new_upperCut_turn
-- name    : OAI.PolynomialVacuumBridge.Corridor.new_upperCut_turn
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T12:15:17.790497+00:00
-- url     : https://prove2.me/theorems/162c4aba-24b6-488c-aa19-df7890582828
-- title:
--   Winding of walks exiting through a cut line
-- statement:
--   A finite vertex set $D$ is admissibly convex if there are integers $\ell_k<h_k$ ($k=0,1,2$) such that $v\in D$ exactly when $\ell_k<t_k(v)<h_k$ for the three tiling coordinates $t_0=2y/\sqrt3$, $t_1=x-y/\sqrt3+\frac12$, $t_2=x+y/\sqrt3+\frac12$ of the position $(x,y)$ of $v$. The star faces of $D$ are the hexagons adjacent to some vertex of $D$; following the boundary of this face set with the star faces on the right gives the star boundary walk. The bottom source is the germ $(\mathrm{up}(0,0),0)$, entering the origin from below. For a domain $D$, $\mathrm{sourceExits}(D)$ is the set of self-avoiding walks from it that stay in $D$ and then leave $D$, and for a direction $k$ and an integer $A$ the cut domain is $\mathrm{upperCut}(D,k,A)=\{v\in D:\mathrm{boxIndex}_k(v)<A\}$. Let $D$ be admissibly convex with the origin in $D$ and the vertex below it outside $D$, let $A>0$, and let $w$ be an exit of the cut domain $\mathrm{upperCut}(D,k,A)$ from the bottom source that is not an exit of $D$. Then
--   $$
--   k=1\implies\mathrm{turnUnits}(w)=-2,\qquad k=2\implies\mathrm{turnUnits}(w)=-1 .
--   $$
--
--   Walks leaving through the new boundary line all exit in the same direction, so their winding is fixed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/ConvexCuts.lean#L131-L152

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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexDomains
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_VisitRecursion
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_BoundaryFlux
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_ConvexCuts

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.new_upperCut_turn (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (hg : bottomSource.1 ∈ D) (hg' : (reverseGerm bottomSource).1 ∉ D)
    (A : ℤ) (hA : 0 < A) (k : Fin 3) (w : List Bool)
    (hw : w ∈ sourceExits (upperCut D k A) bottomSource \ sourceExits D bottomSource) :
    (k = 1 → turnUnits w = -2) ∧ (k = 2 → turnUnits w = -1) := by sorry
