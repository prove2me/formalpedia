-- Prove2me | Theorems.Thm_Kyprianou_Ch02_independentAeCutoffV1
-- name    : Kyprianou.Ch02.independentAeCutoffV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-23T07:47:37.100889+00:00
-- url     : https://prove2.me/theorems/d852cd43-5986-4eb4-af9a-5c5e09df5079
-- title:
--   Preserve family independence under coordinatewise measurable constant replacement and almost-everywhere equality
-- statement:
--   For a family of independent extended nonnegative random variables, replacing a selected coordinate by the constant infinity preserves independence. If a second family is almost everywhere equal to the replaced family coordinatewise, that family is independent. This general lemma transports the finite-intensity Poisson-region count independence to regions of infinite intensity, once the almost-sure infinite-count theorem is available. The decidability of the selected-coordinate predicate is explicit in the formal statement, and may be supplied classically.
-- source:
--   Elementary Mathlib iIndepFun.comp and iIndepFun_congr; needed to discharge Kyprianou.Ch02.pointFamilyCountableCountsIndependentV3 (115918e3-0f06-4a8b-b139-8f88e933e165), connected to Chapter 2 Theorem 2.4.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.independentAeCutoffV1
    {Ω ι : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (H : ι → Prop) [DecidablePred H] (X Y : ι → Ω → ENNReal)
    (hX : iIndepFun X P)
    (hEq : ∀ i, Y i =ᵐ[P] (fun ω => if H i then X i ω else ⊤)) :
    iIndepFun Y P := by sorry
