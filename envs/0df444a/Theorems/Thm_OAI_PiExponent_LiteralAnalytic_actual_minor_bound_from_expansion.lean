-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_bound_from_expansion
-- name    : OAI.PiExponent.LiteralAnalytic.actual_minor_bound_from_expansion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-17T02:34:16.871967+00:00
-- url     : https://prove2.me/theorems/2018fe8e-3b86-4f4b-ab00-c87a679cbad8
-- title:
--   Aggregate a bounded determinant expansion
-- statement:
--   Aggregate a finite determinant expansion using a term-count bound and a common exponential bound on its summands. The definition of analyticRemainder converts the count factor into the claimed exponent.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.LiteralAnalytic.actual_minor_bound_from_expansion {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) (N : ℕ) (terms : Fin N → ℂ) (hexp : (actualMinor d H selection).det = ∑ i, terms i) (hcount : (N : ℝ) ≤ Real.exp ((actualRowCount d H : ℝ) * Real.log (translationTermCount d.m d.v0 H : ℝ))) (hterms : ∀ i, ‖terms i‖ ≤ Real.exp (((actualRowCount d H : ℝ) * H) * (d.analyticError + Collision.collisionRemainder (actualRowCount d H) H + max (-collisionRate d H) (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H))))) : ‖(actualMinor d H selection).det‖ ≤ Real.exp (((actualRowCount d H : ℝ) * H) * (d.analyticError + analyticRemainder d H + max (-collisionRate d H) (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by sorry
