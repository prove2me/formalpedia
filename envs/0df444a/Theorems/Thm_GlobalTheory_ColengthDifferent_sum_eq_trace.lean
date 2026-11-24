-- Prove2me | Theorems.Thm_GlobalTheory_ColengthDifferent_sum_eq_trace
-- name    : GlobalTheory.ColengthDifferent.sum_eq_trace
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:14:37.080425+00:00
-- url     : https://prove2.me/theorems/01953bb9-e9c8-4226-a218-194249f159fd
-- title:
--   Colength Different: sum eq trace
-- statement:
--   The Colength Different construction uses the sum eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColengthDvdOfNeZero.lean#L41-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColengthDvdOfNeZero.lean#L41-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColengthDvdOfNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.ColengthDifferent
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.ColengthDifferent.sum_eq_trace {F : Type} [Field F] [CharZero F] {ι : Type} [Fintype ι]
    (σ : ι → (E →+* F)) (hσ : Function.Injective σ) (hc : Fintype.card ι = Module.finrank ℚ E) (x : E) :
    ∑ i, σ i x = algebraMap ℚ F (Algebra.trace ℚ E x) := by sorry
