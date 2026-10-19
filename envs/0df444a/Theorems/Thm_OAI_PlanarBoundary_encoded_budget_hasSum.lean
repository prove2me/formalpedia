-- Prove2me | Theorems.Thm_OAI_PlanarBoundary_encoded_budget_hasSum
-- name    : OAI.PlanarBoundary.encoded_budget_hasSum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:53:09.399188+00:00
-- url     : https://prove2.me/theorems/c9cf41c7-3aec-4ef6-a63f-b125342a22aa
-- title:
--   The total Peierls budget over all codes
-- statement:
--   With the contour error $\varepsilon_0=\frac12\cdot10^{-14}$, the series over code lengths converges with sum
--   $$
--   \sum_{n\ge0}4n\cdot4^n\,(2\varepsilon_0)^{n/7}=\frac{25}{144}.
--   $$
--
--   Here $4n\cdot4^n$ counts codes of length $n$ and $(2\varepsilon_0)^{n/7}$ bounds each blocking probability.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Peierls.lean#L96-L109

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
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls

open OAI OAI.PlanarBoundary
universe uOmega
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Filter Topology
open Classical _root_.MeasureTheory ProbabilityTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem OAI.PlanarBoundary.encoded_budget_hasSum :
    HasSum (fun n : ℕ => 4*(n : ℝ)*4^n*(2*CriticalScales.contourError)^((n : ℝ)/7)) (25/144 : ℝ) := by sorry
