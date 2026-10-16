-- Prove2me | Theorems.Thm_OAI_Problem310_Auxiliary_thickening_periodic
-- name    : OAI.Problem310.Auxiliary.thickening_periodic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:19:15.124185+00:00
-- url     : https://prove2.me/theorems/c973d22c-c7fa-492c-bcd0-d938908278bc
-- title:
--   Thickenings of 1-periodic subsets of the line are 1-periodic
-- statement:
--   Call $R\subseteq\mathbb{R}$ *1-periodic* if $x+1\in R\iff x\in R$ for all $x\in\mathbb{R}$. For a real number $\varepsilon$, the open $\varepsilon$-thickening of $R$ is
--   $$R_\varepsilon=\{x\in\mathbb{R}:\ \exists\,z\in R,\ |x-z|<\varepsilon\},$$
--   which is empty when $\varepsilon\le 0$.
--
--   **Theorem.** If $R$ is 1-periodic, then $R_\varepsilon$ is 1-periodic for every real $\varepsilon$:
--   $$x+1\in R_\varepsilon\iff x\in R_\varepsilon\qquad\text{for all }x\in\mathbb{R}.$$
--
--   Thickenings are the open neighbourhoods used to enclose a closed periodic set at small cost in measure; this lemma guarantees that the enclosing set stays periodic, so that it can still be analysed on a single period.
--
--   **Formalization Note** The thickening is Mathlib's `Metric.thickening ε R`, defined through the infimum extended distance to $R$; membership is equivalent to the existence of a point of $R$ at distance less than $\varepsilon$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalCenters.lean#L87-L101

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters

open OAI OAI.Problem310 OAI.Problem310.Auxiliary
open Set Filter Topology
open Set Filter Topology MeasureTheory Metric

theorem OAI.Problem310.Auxiliary.thickening_periodic (R : Set ℝ)
    (hR : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ℝ) :
    ∀ x : ℝ, x + 1 ∈ thickening ε R ↔ x ∈ thickening ε R := by sorry
