-- Prove2me | Theorems.Thm_OAI_Problem310_WindowBudget_entropy_tendsto_zero
-- name    : OAI.Problem310.WindowBudget.entropy_tendsto_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:02:35.766653+00:00
-- url     : https://prove2.me/theorems/9f558990-735c-4771-b6af-3025d5761b86
-- title:
--   The entropy factor $20Mr(1+2^{2r+2})e^{-ar}$ tends to zero for $a\ge 10$
-- statement:
--   **Theorem.** For every real number $M$ and every real number $a\ge10$,
--
--   $$\lim_{r\to\infty}\ 20\,M\,r\,\big(1+2^{2r+2}\big)\,e^{-ar}=0,$$
--
--   where $r$ runs through the natural numbers.
--
--   In the dyadic construction the factor $20Mr(1+2^{2r+2})$ bounds the number of representative scales that a union bound over a window of $r$ dyadic exponents has to examine, while $e^{-ar}$ bounds the probability that all trials in the window fail. The lemma says that this exponential saving beats the entropy factor; the proof only uses $a>2\log2$, and $a\ge10$ is the form needed later.
--
--   **Formalization Note** The limit is a `Tendsto ... atTop (nhds 0)` statement for a sequence indexed by natural numbers $r$, cast to $\mathbb{R}$; $M$ is an arbitrary real number, with no sign condition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowBudgets.lean#L19-L55

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope

open OAI OAI.Problem310
open Filter
open scoped Topology

theorem OAI.Problem310.WindowBudget.entropy_tendsto_zero (M a : ℝ) (ha : 10 ≤ a) :
    Tendsto (fun r : ℕ => 20 * M * (r : ℝ) * (1 + (2 : ℝ) ^ (2 * r + 2)) *
      Real.exp (-a * (r : ℝ))) atTop (𝓝 0) := by sorry
