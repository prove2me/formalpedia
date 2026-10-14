-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_weighted_choiceMatrix_permanent_collision_bound
-- name    : OAI.PiExponent.LiteralAnalytic.weighted_choiceMatrix_permanent_collision_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T10:34:48.940712+00:00
-- url     : https://prove2.me/theorems/e850b93d-2bf1-4f65-ab9e-d5dd06d5fc48
-- title:
--   Weighted permanent collision bound for the choice matrix
-- statement:
--   Prove the analytic and collision estimate for the choice-matrix permanent before accounting for the number of permutations. The estimate isolates the squared-multiplicity penalty and the analytic remainder from the generic permutation-count factor.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

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
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_CollisionCombinatorics_Multiplicity
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_RowTranslation_CoreData
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_LiteralAnalyticSummand_InterfaceData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.LiteralAnalytic OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.LiteralAnalytic.weighted_choiceMatrix_permanent_collision_bound
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H) (f : ChoiceFamily d H) :
    (∑ σ : Equiv.Perm (Row d H), ∏ r : Row d H,
        ‖choiceMatrix d selection f r (σ r)‖) ≤
      (Fintype.card (Equiv.Perm (Row d H)) : ℝ) *
        Real.exp
          (-(Real.log 2 / 4) *
            (∑ A : Transverse d H,
              (Collision.multiplicity Finset.univ (fun r => (f r).1) A : ℝ) ^ 2) +
            (actualRowCount d H : ℝ) *
              (H * d.holomorphicError + Real.log 2 / 4 -
                Real.log (1 - Collision.collisionRatio))) := by sorry
