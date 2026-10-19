-- Prove2me | Theorems.Thm_OAI_PlanarBoundary_coordinate_diameter
-- name    : OAI.PlanarBoundary.coordinate_diameter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:44:28.405005+00:00
-- url     : https://prove2.me/theorems/3dfdca16-edbe-484c-9d1e-1a205cd55529
-- title:
--   Closed neighbour cycles have bounded horizontal span
-- statement:
--   Let $v_0,\dots,v_{n-1}$ be points of $\mathbb Z^2$, $n>0$, with consecutive points (cyclically) nearest neighbours. Then for all $i,j$,
--   $$
--   (v_i)_1-(v_j)_1<2n .
--   $$
--
--   It bounds the starting column of a contour code.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/PlanarBoundary.lean#L230-L255

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

theorem OAI.PlanarBoundary.coordinate_diameter {n : ℕ} (hn : 0 < n) (v : Fin n → Point)
    (hedge : ∀ i, Neighbor (v i) (v (FiniteTrails.next hn i))) (i j : Fin n) :
    (v i).1-(v j).1 < 2*(n : ℤ) := by sorry
