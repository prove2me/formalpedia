-- Prove2me | Theorems.Thm_OAI_PlanarBoundary_balanced
-- name    : OAI.PlanarBoundary.balanced
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:42:28.363811+00:00
-- url     : https://prove2.me/theorems/a265708e-e079-49dd-9939-2f7ca0cf4fbd
-- title:
--   The oriented boundary of a cell set is balanced
-- statement:
--   For a finite set $X\subseteq\mathbb Z^2$ of unit cells, the boundary consists of the counterclockwise-oriented sides of cells in $X$ whose outward neighbour is not in $X$; each side has a tail and a head corner, an inside cell and an outside cell. At every corner $v$, the number of boundary sides ending at $v$ equals the number starting at $v$:
--   $$
--   \#\{e:\ \mathrm{head}(e)=v\}=\#\{e:\ \mathrm{tail}(e)=v\}.
--   $$
--
--   So the boundary decomposes into closed trails.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/PlanarBoundary.lean#L44-L63

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

theorem OAI.PlanarBoundary.balanced (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // head e = v} =
      Fintype.card {e : Boundary X // tail e = v} := by sorry
