-- Prove2me | Theorems.Thm_GlobalTheory_spanEquivariant_aeval_map_apply
-- name    : GlobalTheory.spanEquivariant_aeval_map_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:21:21.564425+00:00
-- url     : https://prove2.me/theorems/74b41e9c-6035-46ae-8299-00026fb8244b
-- title:
--   Global Theory: span Equivariant aeval map apply
-- statement:
--   The Global Theory construction uses the span Equivariant aeval map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeneratorMinpolyEigenvalueCompat.lean#L7-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeneratorMinpolyEigenvalueCompat.lean#L7-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeneratorMinpolyEigenvalueCompat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.spanEquivariant_aeval_map_apply {E : Type} [Field E] [NumberField E] {V : Type 1} [AddCommGroup V] [Module ℂ V]
    (P : E →+ V) (b : E) (T : Module.End ℂ V) (hT : ∀ x, T (P x) = P (b * x)) (q : ℚ[X]) :
    ∀ x, aeval T (q.map (algebraMap ℚ ℂ)) (P x) = P (aeval b q * x) := by sorry
