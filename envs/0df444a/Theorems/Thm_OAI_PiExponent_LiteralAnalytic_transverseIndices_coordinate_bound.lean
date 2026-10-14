-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_transverseIndices_coordinate_bound
-- name    : OAI.PiExponent.LiteralAnalytic.transverseIndices_coordinate_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T16:18:46.412197+00:00
-- url     : https://prove2.me/theorems/9a88b05f-f70a-4166-a591-9519d1e12630
-- title:
--   Coordinate bound for transverse indices
-- statement:
--   Every coordinate of a transverse index is strictly below the natural floor of the cutoff plus one. Membership in the weighted simplex and the admissible lower bound on each fixed weight give this bound; for negative cutoffs the index set is empty.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/AnalyticAggregate.lean#L35-L47

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.Log
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.LiteralAnalytic.transverseIndices_coordinate_bound {nu : ℝ}
    (d : FixedData nu) (H : ℝ)
    (a : MatrixTranslation.transverseIndices (fixedWeights d) H)
    (i : Fin d.m) :
    a.1 i < ⌊H⌋₊ + 1 := by
  sorry
