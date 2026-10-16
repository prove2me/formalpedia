-- Prove2me | Theorems.Thm_OAI_Problem310_exists_dyadic_gap_budget
-- name    : OAI.Problem310.exists_dyadic_gap_budget
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T05:22:58.449662+00:00
-- url     : https://prove2.me/theorems/97b01667-cff2-436d-b873-e95deda0ffb1
-- title:
--   A long enough dyadic gap makes $K$ stability costs arbitrarily small
-- statement:
--   For every natural number $K$ and every real number $p>0$ there is a natural number $g\ge2$ such that
--
--   $$
--   K\cdot4\cdot2^{-g}<p .
--   $$
--
--   In the dyadic construction, a stability condition between an earlier grid and a later window separated by a gap of length $g$ costs density $4\cdot2^{-g}$, independently of the grid resolution. This lemma chooses the gap length from the number $K$ of conditions and the budget $p$ alone, so that the total exceptional density $K\cdot4\cdot2^{-g}$ stays below $p$. The side condition $g\ge2$ is what the subsequent density estimate for bad centers requires: it keeps the displacement length within one grid cell.
--
--   **Formalization Note** The power $2^{-g}$ is written as $(2^{-1})^{g}$ and $K$ is cast to a real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridStability.lean#L120-L135

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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridMeasure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridStability

open OAI OAI.Problem310
universe u_ι
open MeasureTheory Set

theorem OAI.Problem310.exists_dyadic_gap_budget (K : ℕ) {p : ℝ} (hp : 0 < p) :
    ∃ g : ℕ, 2 ≤ g ∧ (K : ℝ) * (4 * ((2 : ℝ)⁻¹) ^ g) < p := by sorry
