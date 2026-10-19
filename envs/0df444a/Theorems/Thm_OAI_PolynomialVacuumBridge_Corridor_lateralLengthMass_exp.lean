-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_lateralLengthMass_exp
-- name    : OAI.PolynomialVacuumBridge.Corridor.lateralLengthMass_exp
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T12:29:02.811987+00:00
-- url     : https://prove2.me/theorems/cfabb587-e3a3-46c7-a344-92973d2fcd18
-- title:
--   Exponential tail for the length-weighted mass of far-reaching walks
-- statement:
--   A finite vertex set $D$ is admissibly convex if there are integers $\ell_k<h_k$ ($k=0,1,2$) such that $v\in D$ exactly when $\ell_k<t_k(v)<h_k$ for the three tiling coordinates $t_0=2y/\sqrt3$, $t_1=x-y/\sqrt3+\frac12$, $t_2=x+y/\sqrt3+\frac12$ of the position $(x,y)$ of $v$. The star faces of $D$ are the hexagons adjacent to some vertex of $D$; following the boundary of this face set with the star faces on the right gives the star boundary walk. The bottom source is the germ $(\mathrm{up}(0,0),0)$, entering the origin from below. For a domain $D$, $\mathrm{sourceExits}(D)$ is the set of self-avoiding walks from it that stay in $D$ and then leave $D$, and for a direction $k$ and an integer $A$ the cut domain is $\mathrm{upperCut}(D,k,A)=\{v\in D:\mathrm{boxIndex}_k(v)<A\}$. Let $h\ge1$, let $D$ be admissibly convex, contained in the strip of height $h$ and containing the origin, and let $t\ge0$. Then the length-weighted mass of exits from the bottom source that reach horizontal distance $t$ satisfies
--   $$
--   \sum_{w\ \text{reaches}\ |x|\ge t}|w|\,\lambda^{|w|}\le C\,C_{\mathrm{sp}}\,(h+1)^2\,\exp\Bigl(-\frac c2\cdot\frac t{h+1}\Bigr),
--   $$
--   where $c$ is the tail rate, $C$ the tail constant and $C_{\mathrm{sp}}$ the spatial constant.
--
--   Long walks in a strip are exponentially unlikely to wander far sideways, even after weighting by their length.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/LateralLength.lean#L87-L107

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
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_RaySeparation
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripDecay
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_Reflection
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_LateralMass
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_StripWindows
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_SpatialDecay
import Definitions.Def_OAI_Combinatorics_HoneycombCorridor_LateralLength

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.lateralLengthMass_exp (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (t : ℝ) (ht : 0 ≤ t) :
    lateralLengthMass D t ≤ tailConstant*spatialConstant*((h : ℝ)+1)^2 *
      Real.exp (-(tailRate/2)*t/(h+1)) := by sorry
