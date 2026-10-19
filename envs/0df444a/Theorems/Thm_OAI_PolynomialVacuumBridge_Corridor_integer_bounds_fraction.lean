-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_integer_bounds_fraction
-- name    : OAI.PolynomialVacuumBridge.Corridor.integer_bounds_fraction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:59:53.89454+00:00
-- url     : https://prove2.me/theorems/38232fa9-7cc5-4dc8-b917-ff16da37059e
-- title:
--   Strict real bounds on an integer plus a fraction
-- statement:
--   Let $\ell,h,n$ be integers and $0<a<1$. Then
--   $$
--   \ell<n+a<h\iff\ell\le n<h .
--   $$
--
--   Combined with the fractional offsets of tiling coordinates, this converts the real inequalities defining admissibly convex domains into integer inequalities on box indices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/Convexity.lean#L49-L65

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

theorem OAI.PolynomialVacuumBridge.Corridor.integer_bounds_fraction (lo hi n : ℤ) (a : ℝ) (ha : 0 < a) (ha' : a < 1) :
    ((lo : ℝ) < (n : ℝ)+a ∧ (n : ℝ)+a < (hi : ℝ)) ↔ lo ≤ n ∧ n < hi := by sorry
