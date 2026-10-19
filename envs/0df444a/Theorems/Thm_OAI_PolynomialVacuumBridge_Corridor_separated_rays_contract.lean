-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_separated_rays_contract
-- name    : OAI.PolynomialVacuumBridge.Corridor.separated_rays_contract
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T12:16:12.707589+00:00
-- url     : https://prove2.me/theorems/7be021ff-b3d8-4544-a5e2-f1e8a166d9ef
-- title:
--   Phase separation forces a contraction of positive masses
-- statement:
--   The honeycomb lattice has vertices $\mathrm{up}(i,j)$ and $\mathrm{down}(i,j)$ with $i,j\in\mathbb Z$; $\mathrm{up}(i,j)$ is adjacent to $\mathrm{down}(i,j-1)$, $\mathrm{down}(i,j)$ and $\mathrm{down}(i-1,j)$, reached through slots $0,1,2$. The critical activity is $\lambda=1/(2\cos(\pi/8))$. A germ $g=(v,k)$ is a vertex together with the slot $k$ of the edge through which the walk entered $v$, and a walk from $g$ is encoded by a word $w\in\{\text{left},\text{right}\}^*$ of turns. For a finite set $S$ of words write $|S|_+=\sum_{w\in S}\lambda^{|w|}$ and $\Phi(S)=\sum_{w\in S}\mathrm{wordWeight}(w)$. Let $T\subseteq S$ with $\cos(3\pi/8)\,|T|_+\le\operatorname{Re}\Phi(T)$, and suppose that $\Phi(S)=a\,e^{-i\pi/8}$ for some real $a$ and $\Phi(T)=b\,e^{-i\pi/4}$ with $b\ge0$. Then
--   $$
--   |T|_+\le\rho\,|S|_+,\qquad\rho=\frac1{1+\cos(3\pi/8)\sin(\pi/8)} .
--   $$
--
--   Two families whose phased masses point in directions $\pi/8$ apart cannot have comparable positive masses unless the larger family has extra mass.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/RaySeparation.lean#L55-L112

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

open OAI OAI.PolynomialVacuumBridge OAI.PolynomialVacuumBridge.Corridor

theorem OAI.PolynomialVacuumBridge.Corridor.separated_rays_contract (S T : Finset (List Bool)) (hTS : T ⊆ S)
    (hlower : Real.cos (3*Real.pi/8) * positiveWordMass T ≤ (phasedWordMass T).re)
    (a b : ℝ) (hb : 0 ≤ b)
    (hS : phasedWordMass S = (a : ℂ) * phase (-Real.pi/8))
    (hT : phasedWordMass T = (b : ℂ) * phase (-Real.pi/4)) :
    positiveWordMass T ≤ rayContraction * positiveWordMass S := by sorry
