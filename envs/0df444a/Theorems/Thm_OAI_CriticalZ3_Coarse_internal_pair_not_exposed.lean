-- Prove2me | Theorems.Thm_OAI_CriticalZ3_Coarse_internal_pair_not_exposed
-- name    : OAI.CriticalZ3.Coarse.internal_pair_not_exposed
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:57:02.799426+00:00
-- url     : https://prove2.me/theorems/5d93a983-2136-47e7-9a59-ddc304b22213
-- title:
--   Bits inside two unprocessed blocks are not exposed
-- statement:
--   Coarse blocks at scale $r$: for a planar cell $v$, $Q_r(v)$ is the cube of radius $10r$ around $\bigl((20r+1)v_1,(20r+1)v_2,0\bigr)$; the block bits of $v$ with parent $a$ are the bits of $Q_r(v)$ and (bond model) the interface bonds to $Q_r(a)$; the exposed bits of a set $D$ of cells are the root bits and the blocks of cells in $D$ with their mutual interfaces. Let $0\in D$ and $v,w\notin D$. Every bit internal to the region $Q_r(v)\cup Q_r(w)$ is not among the exposed bits of $D$:
--   $$
--   e\ \text{internal to}\ Q_r(v)\cup Q_r(w)\ \Longrightarrow\ e\notin\mathrm{exposed}(D).
--   $$
--
--   Such bits are therefore still unrevealed when the pair is explored.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Coarse.lean#L296-L346

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

theorem OAI.CriticalZ3.Coarse.internal_pair_not_exposed (m : Model) (r : ℕ) {D : Finset Point}
    (h0 : 0 ∈ D) {v w : Point} (hv : v ∉ D) (hw : w ∉ D) {e : m.Bit}
    (he : m.Internal (PairRegion r v w) e) : e ∉ exposed m r D := by sorry
