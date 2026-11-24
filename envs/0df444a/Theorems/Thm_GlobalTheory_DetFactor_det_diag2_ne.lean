-- Prove2me | Theorems.Thm_GlobalTheory_DetFactor_det_diag2_ne
-- name    : GlobalTheory.DetFactor.det_diag2_ne
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:43:10.584423+00:00
-- url     : https://prove2.me/theorems/5a089ad3-f4a6-4445-9631-c76d7b951dae
-- title:
--   Det Factor: det diag2 ne
-- statement:
--   The Det Factor construction uses the det diag2 ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L30-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GlCharacterFactorsThroughDetOfTwoNeZero.lean#L30-L34

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

theorem GlobalTheory.DetFactor.det_diag2_ne {n : ℕ} (h2 : (2 : k) ≠ 0) (i : Fin n) :
    (diagonal (fun l => if l = i then (2 : k) else 1)).det ≠ 0 := by sorry
