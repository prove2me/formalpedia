-- Prove2me | Theorems.Thm_OAI_CriticalZ3_Coarse_Exploration_badMass_bound
-- name    : OAI.CriticalZ3.Coarse.Exploration.badMass_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:03:45.605352+00:00
-- url     : https://prove2.me/theorems/4d4eedfd-feda-4969-933d-e19e595e5ba4
-- title:
--   Each exploration step declares a cell bad with tiny probability
-- statement:
--   The coarse exploration at scale $r$ processes planar cells $v$ in queue order: it reveals the unknown bits of the block of $v$ (the cube $Q_r(v)$ of radius $10r$ around $((20r+1)v_1,(20r+1)v_2,0)$, with the interface to its parent), accepts $v$ as good if its packet event holds and all unvisited neighbours are likely given the revealed bits, and otherwise marks it bad. For scale data $s_c$ and a valid exploration state $s$ at scale $r$ with parameters $q,\delta$, the probability that the next processed cell is declared bad is at most the contour error:
--   $$
--   \mathrm{badMass}(s)\le\varepsilon_0=\tfrac12\cdot10^{-14}.
--   $$
--
--   Together with the hitting bound this gives the Peierls estimate for bad cells.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ExplorationInvariant.lean#L106-L170

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

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse OAI.CriticalZ3.Coarse.Exploration
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable {m : Model} {r : ℕ}

theorem OAI.CriticalZ3.Coarse.Exploration.badMass_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) :
    (scheme (r := sc.r) sc.q sc.δ).badMass s ≤ CriticalScales.contourError := by sorry
