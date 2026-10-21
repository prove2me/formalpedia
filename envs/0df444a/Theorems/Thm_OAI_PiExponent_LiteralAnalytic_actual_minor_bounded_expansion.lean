-- Prove2me | Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_bounded_expansion
-- name    : OAI.PiExponent.LiteralAnalytic.actual_minor_bounded_expansion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T02:36:00.168977+00:00
-- url     : https://prove2.me/theorems/31bd4432-a19c-456d-b195-33f9611d4f8d
-- title:
--   Bounded translated expansion of the actual minor
-- statement:
--   Expand the determinant as a finite sum over translated choices, with at most the translation count to the power of the row count many terms, and use the translated-summand estimate to bound every term.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Analysis/LiteralAnalyticSummand.lean#L177-L199

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem OAI.PiExponent.LiteralAnalytic.actual_minor_bounded_expansion {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H) : ∃ (N : ℕ) (terms : Fin N → ℂ), (actualMinor d H selection).det = ∑ i, terms i ∧ (N : ℝ) ≤ Real.exp ((actualRowCount d H : ℝ) * Real.log (translationTermCount d.m d.v0 H : ℝ)) ∧ ∀ i, ‖terms i‖ ≤ Real.exp (((actualRowCount d H : ℝ) * H) * (d.analyticError + Collision.collisionRemainder (actualRowCount d H) H + max (-collisionRate d H) (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)))) := by sorry
