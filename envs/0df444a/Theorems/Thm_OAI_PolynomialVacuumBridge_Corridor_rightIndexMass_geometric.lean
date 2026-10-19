-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_rightIndexMass_geometric
-- name    : OAI.PolynomialVacuumBridge.Corridor.rightIndexMass_geometric
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T12:16:59.22843+00:00
-- url     : https://prove2.me/theorems/036ea5fe-a0ef-43f7-b5a9-552dc89d5f8e
-- title:
--   Geometric decay of walks travelling to the right in a strip
-- statement:
--   A finite vertex set $D$ is admissibly convex if there are integers $\ell_k<h_k$ ($k=0,1,2$) such that $v\in D$ exactly when $\ell_k<t_k(v)<h_k$ for the three tiling coordinates $t_0=2y/\sqrt3$, $t_1=x-y/\sqrt3+\frac12$, $t_2=x+y/\sqrt3+\frac12$ of the position $(x,y)$ of $v$. The star faces of $D$ are the hexagons adjacent to some vertex of $D$; following the boundary of this face set with the star faces on the right gives the star boundary walk. The bottom source is the germ $(\mathrm{up}(0,0),0)$, entering the origin from below. For a domain $D$, $\mathrm{sourceExits}(D)$ is the set of self-avoiding walks from it that stay in $D$ and then leave $D$, and for a direction $k$ and an integer $A$ the cut domain is $\mathrm{upperCut}(D,k,A)=\{v\in D:\mathrm{boxIndex}_k(v)<A\}$. Let $h\ge1$ and let $D$ be admissibly convex, contained in the strip of height $h$ (layers $0\le j<h$) and containing the origin. Let $\mathrm{rightIndexMass}(D,A)$ be the total weight $\sum\lambda^{|w|}$ of exits of $D$ from the bottom source that reach box index $1$ at least $A$. Then for every $n$,
--   $$
--   \mathrm{rightIndexMass}(D,nh)\le\frac{\rho^n}{\cos(3\pi/8)},\qquad\rho=\frac1{1+\cos(3\pi/8)\sin(\pi/8)}<1 .
--   $$
--
--   Each further horizontal distance $h$ costs a fixed factor $\rho$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/StripDecay.lean#L107-L122

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

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.rightIndexMass_geometric (h : ℕ) (hh : 1 ≤ h) (D : Finset Vertex)
    (hD : AdmissiblyConvex D) (hg : bottomSource.1 ∈ D)
    (hstrip : ∀ v ∈ D, InStrip h v) (n : ℕ) :
    rightIndexMass D ((n : ℤ)*h) ≤ (Real.cos (3*Real.pi/8))⁻¹ * rayContraction ^ n := by sorry
