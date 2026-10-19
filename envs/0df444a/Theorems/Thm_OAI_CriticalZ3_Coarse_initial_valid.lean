-- Prove2me | Theorems.Thm_OAI_CriticalZ3_Coarse_initial_valid
-- name    : OAI.CriticalZ3.Coarse.initial_valid
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:07:57.632799+00:00
-- url     : https://prove2.me/theorems/9a7777e5-9572-451a-9e6a-e051f82f1715
-- title:
--   The initial exploration state is valid
-- statement:
--   The coarse exploration at scale $r$ processes planar cells $v$ in queue order: it reveals the unknown bits of the block of $v$ (the cube $Q_r(v)$ of radius $10r$ around $((20r+1)v_1,(20r+1)v_2,0)$, with the interface to its parent), accepts $v$ as good if its packet event holds and all unvisited neighbours are likely given the revealed bits, and otherwise marks it bad. For scale data $s_c$, the initial state at scale $r$ is valid for $q,\delta$. In this state the root bits are known and open, cell $0$ is processed, and the queue holds the four children of the root packet:
--   $$
--   \mathbb P_q(\text{child event}\mid\text{root bits open})>1-\delta\quad\text{for each child}.
--   $$
--
--   This starts the exploration from the root block.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ExplorationConnectivity.lean#L164-L188

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
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse
import Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals
import Definitions.Def_OAI_Probability_CriticalZ3_Exploration
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationInvariant
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationConnectivity

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning

theorem OAI.CriticalZ3.Coarse.initial_valid {m : Model} (sc : ScaleData m) : (initial m sc.r).Valid sc.q sc.δ := by sorry
