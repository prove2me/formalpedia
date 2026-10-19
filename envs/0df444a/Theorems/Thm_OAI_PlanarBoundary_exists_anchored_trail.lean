-- Prove2me | Theorems.Thm_OAI_PlanarBoundary_exists_anchored_trail
-- name    : OAI.PlanarBoundary.exists_anchored_trail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:46:59.640995+00:00
-- url     : https://prove2.me/theorems/fd37e72d-6ffe-48a0-8f56-5aadcc0686fc
-- title:
--   A boundary trail crossing the ray near the origin
-- statement:
--   For a finite set $X\subseteq\mathbb Z^2$ of unit cells, the boundary consists of the counterclockwise-oriented sides of cells in $X$ whose outward neighbour is not in $X$; each side has a tail and a head corner, an inside cell and an outside cell. If $(0,0)\in X$, there is a closed trail of $n>0$ distinct boundary sides, each starting where the previous ends, containing a side with nonzero ray flux whose tail has first coordinate
--   $$
--   0<x<2n .
--   $$
--
--   The crossing side anchors the contour to a bounded set of starting positions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/PlanarBoundary.lean#L257-L285

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary

open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical
open Classical

theorem OAI.PlanarBoundary.exists_anchored_trail (X : Finset Point) (hX : (0,0) ∈ X) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ e : Fin n → Boundary X,
      Function.Injective e ∧
      (∀ i, tail (e (FiniteTrails.next hn i)) = head (e i)) ∧
      ∃ i, 0 < (tail (e i)).1 ∧ (tail (e i)).1 < 2*(n : ℤ) ∧
        rayFlux (tail (e i)) (head (e i)) ≠ 0 := by sorry
