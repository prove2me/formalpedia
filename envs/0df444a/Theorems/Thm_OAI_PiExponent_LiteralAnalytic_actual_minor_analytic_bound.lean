-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_analytic_bound
-- name    : OAI.PiExponent.LiteralAnalytic.actual_minor_analytic_bound
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-11T20:24:19.071996+00:00
-- url     : https://prove2.me/theorems/a08a3f36-e4a6-4a12-a77b-53e5c07f6ac9
-- title:
--   The original selected-minor analytic bound
-- statement:
--   For the original fixed datum $d$, $\nu\ge0$, height $H>0$, and a column selection with nonzero selected-minor determinant, the normalized logarithmic determinant is at most $d.analyticError+R_d(H)+\max\{-collisionRate_d(H),-\nu((d.A)(1-d.eta)-actualMean_d(H))\}$, with every term and binder exactly as in the source theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticAggregate.lean#L53-L72

import Definitions.Def_OAI_PiExponent_ApproximationDefinitions
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_DeterminantContradiction_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.LiteralAnalytic.actual_minor_analytic_bound {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H)
    (hne : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
      d.analyticError + analyticRemainder d H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) := by
  sorry
