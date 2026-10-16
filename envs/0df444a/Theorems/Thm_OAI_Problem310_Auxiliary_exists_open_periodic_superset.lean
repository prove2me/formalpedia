-- Prove2me | Theorems.Thm_OAI_Problem310_Auxiliary_exists_open_periodic_superset
-- name    : OAI.Problem310.Auxiliary.exists_open_periodic_superset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:19:43.734092+00:00
-- url     : https://prove2.me/theorems/86eef7b5-4e3c-4fb6-b8d1-366ed44a134f
-- title:
--   A closed 1-periodic set has open 1-periodic neighbourhoods of almost the same density
-- statement:
--   Write $\lambda$ for Lebesgue measure on $\mathbb{R}$, and call $R\subseteq\mathbb{R}$ *1-periodic* if $x+1\in R\iff x\in R$ for all $x\in\mathbb{R}$.
--
--   **Theorem.** Let $R\subseteq\mathbb{R}$ be closed and 1-periodic, and let $\varepsilon>0$. Then there is an open, 1-periodic set $V\subseteq\mathbb{R}$ with $R\subseteq V$ and
--   $$\lambda\bigl(V\cap[0,1]\bigr)\le\lambda\bigl(R\cap[0,1]\bigr)+\varepsilon .$$
--
--   This is a periodic form of outer regularity: a closed periodic set can be enlarged to an open periodic set at arbitrarily small extra cost in measure per period. It is used to cover the exceptional centers of a random construction by an open periodic set before adding them to the hitting set.
--
--   **Formalization Note** Measures are extended nonnegative reals, and $\varepsilon$ enters as `ENNReal.ofReal ε`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalCenters.lean#L103-L127

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

theorem OAI.Problem310.Auxiliary.exists_open_periodic_superset (R : Set ℝ) (hRc : IsClosed R)
    (hRp : ∀ x : ℝ, x + 1 ∈ R ↔ x ∈ R) (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set ℝ, IsOpen V ∧
      (∀ x : ℝ, x + 1 ∈ V ↔ x ∈ V) ∧ R ⊆ V ∧
      volume (V ∩ Icc (0 : ℝ) 1) ≤
        volume (R ∩ Icc (0 : ℝ) 1) + ENNReal.ofReal ε := by sorry
