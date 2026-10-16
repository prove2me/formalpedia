-- Prove2me | Theorems.Thm_OAI_Problem310_RoutingBudget_exists_nondefault_parameters
-- name    : OAI.Problem310.RoutingBudget.exists_nondefault_parameters
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:03:53.776197+00:00
-- url     : https://prove2.me/theorems/0284a3fd-a31f-4651-83ac-e1b9002bc5c9
-- title:
--   Choice of branching number, depth and window threshold for the dyadic router
-- statement:
--   **Theorem.** For every real number $p$ with $0<p<1$ there exist integers $M\ge1$, $d\ge1$ and $R\ge1$ such that
--
--   $$\frac{pM}{2}\ge10\qquad\text{and}\qquad\big(1-2^{-M}\big)^{d}<p,$$
--
--   and such that for every integer $r\ge R$ and every integer $N$ with $0\le N\le 1+M\,r\,2^{2r+2}$,
--
--   $$N\Big(1-\frac p2\Big)^{Mr}<p.$$
--
--   These are the parameters of the dyadic router: $M$ is the number of nondefault children of a node (so there are $M+1$ children), $d$ is the depth of the tree, and $R$ is a lower bound for window lengths. The quantity $(1-2^{-M})^d$ is the probability that the route of a fixed point never takes the default child, given that at each node the default is chosen exactly when all $M$ fair selectors fail, an event of probability $2^{-M}$. The last inequality is the union-bound budget over at most $1+Mr2^{2r+2}$ representative scales, each failing with probability $(1-p/2)^{Mr}$.
--
--   **Formalization Note** Lean states the last inequality in `ENNReal` as `(N : ENNReal) * (ENNReal.ofReal (1 - p / 2)) ^ (M * r) < ENNReal.ofReal p`; since $1-p/2>0$ this is equivalent to the real inequality above. The bound $1+Mr2^{2r+2}$ is a natural-number expression.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RoutingBudget.lean#L18-L51

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

theorem OAI.Problem310.RoutingBudget.exists_nondefault_parameters (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ M d R : ℕ, 1 ≤ M ∧ 1 ≤ d ∧ 1 ≤ R ∧
      10 ≤ p * (M : ℝ) / 2 ∧
      (1 - ((2 : ℝ)⁻¹) ^ M) ^ d < p ∧
      ∀ r : ℕ, R ≤ r → ∀ N : ℕ,
        N ≤ 1 + M * r * 2 ^ (2 * r + 2) →
        (N : ENNReal) * (ENNReal.ofReal (1 - p / 2)) ^ (M * r) <
          ENNReal.ofReal p := by sorry
