-- Prove2me | Theorems.Thm_OAI_Problem310_WindowBudget_exists_probability_threshold
-- name    : OAI.Problem310.WindowBudget.exists_probability_threshold
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:03:12.961533+00:00
-- url     : https://prove2.me/theorems/4b725b72-4771-4db2-85f5-f4c1020cd617
-- title:
--   Window-length threshold beyond which $20Mr(1+2^{2r+2})(1-p/2)^{(M-1)r}<p$
-- statement:
--   **Theorem.** Let $p$ be a real number with $0<p<1$, and let $M\ge2$ be an integer such that
--
--   $$\frac{p\,(M-1)}{2}\ge10.$$
--
--   Then there is an integer $r_0\ge1$ such that for every integer $r\ge r_0$
--
--   $$20\,M\,r\,\big(1+2^{2r+2}\big)\Big(1-\frac p2\Big)^{(M-1)r}<p.$$
--
--   Here $M$ plays the role of the total number of children of a node of the dyadic router, $M-1$ of which are nondefault. For a window of $r$ exponents, $(1-p/2)^{(M-1)r}$ is the probability that all $(M-1)r$ independent trials fail at one scale (each succeeds with probability $p/2$), and $20Mr(1+2^{2r+2})$ bounds the number of representative scales; the lemma provides one window length $r_0$ beyond which this union bound stays below $p$.
--
--   **Formalization Note** $M$ is a natural number and the exponent $(M-1)r$ is computed in $\mathbb{N}$; since $M\ge2$, this is the usual difference.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/WindowBudgets.lean#L123-L142

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

theorem OAI.Problem310.WindowBudget.exists_probability_threshold (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (M : ℕ) (hM : 2 ≤ M) (hmargin : 10 ≤ p * ((M : ℝ) - 1) / 2) :
    ∃ r₀ : ℕ, 1 ≤ r₀ ∧ ∀ r : ℕ, r₀ ≤ r →
      20 * (M : ℝ) * (r : ℝ) * (1 + (2 : ℝ) ^ (2 * r + 2)) *
        (1 - p / 2) ^ ((M - 1) * r) < p := by sorry
