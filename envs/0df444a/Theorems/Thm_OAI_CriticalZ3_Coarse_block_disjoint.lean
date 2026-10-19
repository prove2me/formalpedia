-- Prove2me | Theorems.Thm_OAI_CriticalZ3_Coarse_block_disjoint
-- name    : OAI.CriticalZ3.Coarse.block_disjoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:56:01.822995+00:00
-- url     : https://prove2.me/theorems/f17d8c78-e26e-4608-9074-779f1e2d2189
-- title:
--   Blocks of distinct unprocessed cells are disjoint
-- statement:
--   Coarse blocks at scale $r$: for a planar cell $v$, $Q_r(v)$ is the cube of radius $10r$ around $\bigl((20r+1)v_1,(20r+1)v_2,0\bigr)$; the block bits of $v$ with parent $a$ are the bits of $Q_r(v)$ and (bond model) the interface bonds to $Q_r(a)$; the exposed bits of a set $D$ of cells are the root bits and the blocks of cells in $D$ with their mutual interfaces. For distinct cells $v\ne w$ outside a set $D$ with parents $a,b\in D$, the block bits are disjoint:
--   $$
--   \mathrm{block}(v,a)\cap\mathrm{block}(w,b)=\varnothing .
--   $$
--
--   Hence blocks of different queued cells are revealed independently.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Coarse.lean#L260-L275

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

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Coarse
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical

theorem OAI.CriticalZ3.Coarse.block_disjoint (m : Model) (r : ℕ) {D : Finset Point} {v w a b : Point}
    (hv : v ∉ D) (hw : w ∉ D) (ha : a ∈ D) (hb : b ∈ D) (hvw : v ≠ w) :
    Disjoint (block m r v a) (block m r w b) := by sorry
