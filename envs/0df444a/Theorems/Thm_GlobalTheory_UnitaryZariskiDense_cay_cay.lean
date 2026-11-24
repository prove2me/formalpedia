-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryZariskiDense_cay_cay
-- name    : GlobalTheory.UnitaryZariskiDense.cay_cay
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:46:21.923205+00:00
-- url     : https://prove2.me/theorems/0e6582e2-9fd5-4984-a76f-0236d4fcd2d8
-- title:
--   Unitary Zariski Dense: cay cay
-- statement:
--   The Unitary Zariski Dense construction uses the cay cay property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L108-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L108-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}

theorem GlobalTheory.UnitaryZariskiDense.cay_cay {n : Type} [Fintype n] [DecidableEq n] (B : Matrix n n ℂ) (hB : (1 + B).det ≠ 0) :
    (1 + cay B).det ≠ 0 ∧ cay (cay B) = B := by sorry
