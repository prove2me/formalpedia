-- Prove2me | Theorems.Thm_OAI_CriticalZ3_Coarse_Exploration_hit_of_bad_subset
-- name    : OAI.CriticalZ3.Coarse.Exploration.hit_of_bad_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T20:06:44.16299+00:00
-- url     : https://prove2.me/theorems/8270a255-8240-445e-b240-be788c571f09
-- title:
--   Cells declared bad are hit by the revealing scheme
-- statement:
--   The coarse exploration at scale $r$ processes planar cells $v$ in queue order: it reveals the unknown bits of the block of $v$ (the cube $Q_r(v)$ of radius $10r$ around $((20r+1)v_1,(20r+1)v_2,0)$, with the interface to its parent), accepts $v$ as good if its packet event holds and all unvisited neighbours are likely given the revealed bits, and otherwise marks it bad. An adaptive revealing scheme has states $s$; each state reveals a finite set of bits under a product law with parameters $p_s$, may visit a vertex, declares it bad or not according to the revealed values, and moves to a child state whose parameters fix the revealed bits. The bad mass of $s$ is the probability that the revealed values are declared bad; "$U$ is hit within $n$ steps" means every vertex of $U$ is visited and declared bad at its first visit. If $s$ is valid and coloured, $U$ is disjoint from the processed cells of $s$, and every cell of $U$ is bad after $n$ steps of the run, then $U$ is hit within $n$ steps by the exploration's revealing scheme:
--   $$
--   U\subseteq\mathrm{bad}(\mathrm{run}_n(s,\omega))\ \Longrightarrow\ \omega\in\mathrm{hit}_n(s,U).
--   $$
--
--   So the probability that a set of cells is declared bad is at most $\varepsilon_0^{|U|}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ExplorationProbability.lean#L83-L132

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

theorem OAI.CriticalZ3.Coarse.Exploration.hit_of_bad_subset {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (n : ℕ) (ω : m.Config) (U : Finset Point)
    (hd : Disjoint U s.processed) (hU : U ⊆ (run q δ n s ω).bad) :
    ω ∈ (scheme (r := r) q δ).hit n s U := by sorry
