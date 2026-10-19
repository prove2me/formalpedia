-- Prove2me | Theorems.Thm_OAI_PolynomialVacuumBridge_Corridor_finite_indicator_row_containment
-- name    : OAI.PolynomialVacuumBridge.Corridor.finite_indicator_row_containment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T12:04:07.424509+00:00
-- url     : https://prove2.me/theorems/1a34ed41-f242-455e-9d9e-9b4824512f52
-- title:
--   A zero-one potential with matching jumps lies inside a row-convex set
-- statement:
--   Let $p:\mathbb Z^2\to\mathbb Z$ be finitely supported with values in $\{0,1\}$, and let $S\subset\mathbb Z^2$ be finite. Suppose that wherever $p$ jumps along a row, the jump agrees with that of the indicator of $S$:
--   $$
--   p(i,j)\ne p(i-1,j)\implies p(i,j)-p(i-1,j)=\mathbf 1_S(i,j)-\mathbf 1_S(i-1,j).
--   $$
--   Suppose also that every row of $S$ is an interval, i.e. $(i_1,j),(i_2,j)\in S$ and $i_1\le i\le i_2$ imply $(i,j)\in S$. Then $\operatorname{supp}p\subseteq S$.
--
--   So a $\{0,1\}$ potential whose row jumps match those of a row-convex set lives inside that set.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/HoneycombCorridor/BoundaryContainment.lean#L61-L110

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

theorem OAI.PolynomialVacuumBridge.Corridor.finite_indicator_row_containment (p : FaceIndex →₀ ℤ) (S : Finset FaceIndex)
    (hval : ∀ a, p a = 0 ∨ p a = 1)
    (hgrad : ∀ i j : ℤ, p (i,j) ≠ p (i-1,j) →
      p (i,j) - p (i-1,j) = faceIndicator S (i,j) - faceIndicator S (i-1,j))
    (hrow : ∀ i₁ i i₂ j : ℤ, i₁ ≤ i → i ≤ i₂ → (i₁,j) ∈ S → (i₂,j) ∈ S →
      (i,j) ∈ S) : p.support ⊆ S := by sorry
