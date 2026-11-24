-- Prove2me | Theorems.Thm_GlobalTheory_DetFactor_conj_transvection
-- name    : GlobalTheory.DetFactor.conj_transvection
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:29.914875+00:00
-- url     : https://prove2.me/theorems/d038cd23-dfc8-4435-a918-bcab304836ca
-- title:
--   Det Factor: conj transvection
-- statement:
--   The Det Factor construction uses the conj transvection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L22-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GlCharacterFactorsThroughDetOfTwoNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory GlobalTheory.DetFactor
variable {k : Type} [Field k] {m : ℕ}

theorem GlobalTheory.DetFactor.conj_transvection {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : k) :
    diagonal (fun l => if l = i then (2 : k) else 1) * transvection i j t
      = transvection i j (2 * t) * diagonal (fun l => if l = i then (2 : k) else 1) := by sorry
