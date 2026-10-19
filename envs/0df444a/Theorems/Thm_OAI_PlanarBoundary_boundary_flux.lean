-- Prove2me | Theorems.Thm_OAI_PlanarBoundary_boundary_flux
-- name    : OAI.PlanarBoundary.boundary_flux
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:43:49.027807+00:00
-- url     : https://prove2.me/theorems/46aaa321-f5cb-44aa-bcf6-753760253a42
-- title:
--   The boundary winds once around a contained cell
-- statement:
--   For a finite set $X\subseteq\mathbb Z^2$ of unit cells, the boundary consists of the counterclockwise-oriented sides of cells in $X$ whose outward neighbour is not in $X$; each side has a tail and a head corner, an inside cell and an outside cell. The total signed crossing number of the boundary sides with the positive horizontal ray from the centre of the cell $(0,0)$ is
--   $$
--   \sum_{e}\mathrm{flux}(e)=\begin{cases}1&(0,0)\in X,\\0&\text{otherwise}.\end{cases}
--   $$
--
--   This is a discrete winding-number identity.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/PlanarBoundary.lean#L153-L174

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

theorem OAI.PlanarBoundary.boundary_flux (X : Finset Point) :
    (∑ e : Boundary X, rayFlux (tail e) (head e)) = if (0,0) ∈ X then 1 else 0 := by sorry
