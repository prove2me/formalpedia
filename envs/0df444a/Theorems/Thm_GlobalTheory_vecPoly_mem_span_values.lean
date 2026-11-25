-- Prove2me | Theorems.Thm_GlobalTheory_vecPoly_mem_span_values
-- name    : GlobalTheory.vecPoly_mem_span_values
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:53:23.58733+00:00
-- url     : https://prove2.me/theorems/c0a87f33-4ce1-43bc-9c72-28e2c0e4348b
-- title:
--   Global Theory: vec Poly mem span values
-- statement:
--   The Global Theory construction uses the vec Poly mem span values property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/VecPolyMemSpanValues.lean#L5-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/VecPolyMemSpanValues.lean#L5-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_VecPolyMemSpanValues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.vecPoly_mem_span_values (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (Z : ℂ → V)
    (X : ℕ → V) (ν : Fin n → ℂ) (hν : Function.Injective ν)
    (hZ : ∀ s : ℂ, Z s = ∑ j ∈ Finset.range n, s ^ j • X j) :
    (∀ j, j < n → X j ∈ Submodule.span ℂ (Set.range fun i => Z (ν i))) ∧
      ∀ s : ℂ, Z s ∈ Submodule.span ℂ (Set.range fun i => Z (ν i)) := by sorry
