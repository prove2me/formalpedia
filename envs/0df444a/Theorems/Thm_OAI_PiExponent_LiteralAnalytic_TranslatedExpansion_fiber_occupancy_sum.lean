-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_TranslatedExpansion_fiber_occupancy_sum
-- name    : OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.fiber_occupancy_sum
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T03:06:38.769349+00:00
-- url     : https://prove2.me/theorems/6556a51e-0cd1-4730-9a2b-7e03b510ec0b
-- title:
--   Counting occupancy through finite fibers
-- statement:
--   The sum of the cardinalities of the fibers over keys satisfying P equals the number of indices whose key satisfies P. This removes the parent's finite-fiber counting step. It can be proved by counting index-fiber pairs in two ways, with no positivity or nonemptiness assumptions; the empty types and empty selected set both give zero.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
open scoped BigOperators

theorem OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.fiber_occupancy_sum
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (P : κ → Prop) [DecidablePred P] :
    (∑ a ∈ ((Finset.univ : Finset κ).filter P),
      (((Finset.univ : Finset ι).filter (fun i => group i = a)).card : ℝ)) =
      (((Finset.univ : Finset ι).filter (fun i => P (group i))).card : ℝ) := by sorry
