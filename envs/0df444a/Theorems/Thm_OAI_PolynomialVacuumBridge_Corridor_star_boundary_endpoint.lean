-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_star_boundary_endpoint
-- name    : OAI.PolynomialVacuumBridge.Corridor.star_boundary_endpoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T12:05:45.381023+00:00
-- url     : https://prove2.me/theorems/1cd2172c-1f80-4392-acd8-b4f8ad5b8c1b
-- title:
--   Exits of walks from the star boundary land on the boundary loop
-- statement:
--   A finite vertex set $D$ is admissibly convex if there are integers $\ell_k<h_k$ ($k=0,1,2$) such that $v\in D$ exactly when $\ell_k<t_k(v)<h_k$ for the three tiling coordinates $t_0=2y/\sqrt3$, $t_1=x-y/\sqrt3+\frac12$, $t_2=x+y/\sqrt3+\frac12$ of the position $(x,y)$ of $v$. The star faces of $D$ are the hexagons adjacent to some vertex of $D$; following the boundary of this face set with the star faces on the right gives the star boundary walk. Let $D$ be admissibly convex and let $g$ be a germ on the star face boundary where the boundary walk turns right, such that the boundary walk from $g$ closes into a simple loop after $n>0$ steps. Let $e=\mathrm{advance}(g,\text{left})$ be the germ entering $D$ next to $g$. If $w$ is a walk from $e$ that stays in $D$ and ends at a vertex outside $D$ whose predecessor is in $D$, then
--   $$
--   \mathrm{end}(e,w)\in\mathrm{traced}(\text{star boundary loop}).
--   $$
--
--   Every exit point of a walk in a convex domain lies on the star boundary loop.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/BoundaryContainment.lean#L147-L211

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

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.star_boundary_endpoint (D : Finset Vertex) (hD : AdmissiblyConvex D)
    (g : FaceBoundary (starFaces D)) (n : ℕ) (hn : 0 < n)
    (hN : (traced g.val (faceBoundaryWord (starFaces D) g n)).Nodup)
    (hc : terminalGerm g.val (faceBoundaryWord (starFaces D) g n) = g.val)
    (hg : faceBoundaryTurn (starFaces D) g.val = false)
    (e : Germ) (w : List Bool) (he : e = advance g.val true)
    (hd : ∀ v ∈ traced e w, v ∈ D)
    (hu : (terminalGerm e w).1 ∉ D)
    (hu' : (reverseGerm (terminalGerm e w)).1 ∈ D) :
    (terminalGerm e w).1 ∈ traced g.val (faceBoundaryWord (starFaces D) g n) := by sorry
