-- Prove2me | Theorems.Thm_GlobalTheory_finiteDimensional_span_multilinear_values
-- name    : GlobalTheory.finiteDimensional_span_multilinear_values
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:26:45.343596+00:00
-- url     : https://prove2.me/theorems/638c2c63-0e76-4fa7-8318-ecd6cc774c60
-- title:
--   Global Theory: finite Dimensional span multilinear values
-- statement:
--   The Global Theory construction uses the finite Dimensional span multilinear values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FiniteDimensionalSpanMultilinearValues.lean#L5-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FiniteDimensionalSpanMultilinearValues.lean#L5-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FiniteDimensionalSpanMultilinearValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.finiteDimensional_span_multilinear_values :
    ∀ {ι : Type} [Fintype ι] (E : ι → Type) [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
      (F : Type) [AddCommGroup F] [Module ℂ F] (T : MultilinearMap ℂ E F)
      (W : ∀ i, Submodule ℂ (E i)), (∀ i, FiniteDimensional ℂ (W i)) →
      FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ v : ∀ i, E i, (∀ i, v i ∈ W i) ∧ f = T v}) := by sorry
