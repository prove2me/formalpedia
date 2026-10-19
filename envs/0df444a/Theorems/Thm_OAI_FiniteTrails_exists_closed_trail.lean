-- Prove2me | Theorems.Thm_OAI_FiniteTrails_exists_closed_trail
-- name    : OAI.FiniteTrails.exists_closed_trail
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:41:13.678106+00:00
-- url     : https://prove2.me/theorems/ebd3ce32-d520-49c4-a0eb-632e678662da
-- title:
--   Balanced directed edge sets contain a closed trail of nonzero weight
-- statement:
--   Let finitely many directed edges with tails and heads in $V$ be balanced (at each vertex, as many edges enter as leave), and let $w$ be integer weights with nonzero total. Then there is a closed trail of distinct edges $e_0,\dots,e_{n-1}$, $n>0$, with nonzero weight:
--   $$
--   \mathrm{tail}(e_{i+1\bmod n})=\mathrm{head}(e_i),\qquad\sum_iw(e_i)\ne0 .
--   $$
--
--   Applied to boundaries of planar cell sets, it yields a contour around the origin.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/FiniteTrails.lean#L81-L107

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

open OAI OAI.FiniteTrails
universe uD uV
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology
open scoped ENNReal BigOperators Matrix
open Classical Function
variable {D : Type uD} {V : Type uV} [Fintype D]

theorem OAI.FiniteTrails.exists_closed_trail (tail head : D → V)
    (hbal : ∀ v, Fintype.card {d // head d = v} = Fintype.card {d // tail d = v})
    (w : D → ℤ) (hw : ∑ d, w d ≠ 0) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∃ e : Fin n → D, Function.Injective e ∧
      (∀ i : Fin n, tail (e (next hn i)) = head (e i)) ∧ (∑ i, w (e i)) ≠ 0 := by sorry
