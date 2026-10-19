-- Prove2me | Theorems.Thm_OAI_CriticalZ3_exists_scales
-- name    : OAI.CriticalZ3.exists_scales
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:36:13.108983+00:00
-- url     : https://prove2.me/theorems/c6bed017-455b-406b-9d76-02caf5f41c2f
-- title:
--   Supercritical parameters admit scale data
-- statement:
--   For bond or site percolation on $\mathbb Z^3$, let $0<p<1$ and suppose the origin belongs to an infinite cluster with positive probability:
--   $$
--   \mathbb P_p\bigl(|\mathcal C(0)|=\infty\bigr)>0 .
--   $$
--   Then there are scale data with this $p$: tolerances, a seed size, numbers $K,R,r$, and $q\in(p/2,p)$ satisfying all budget inequalities and the quarter-face crossing bounds.
--
--   These scale data are the input to the coarse exploration.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Scales.lean#L143-L183

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

open OAI OAI.CriticalZ3
open _root_.MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Filter Topology
open _root_.MeasureTheory ProbabilityTheory Classical

theorem OAI.CriticalZ3.exists_scales (model : Model) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hInf : 0 < model.law p (model.InfiniteAt 0)) : ∃ s : ScaleData model, s.p = p := by sorry
