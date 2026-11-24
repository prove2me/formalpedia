-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_colSub_mul
-- name    : GlobalTheory.MinorFrame.colSub_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:13.697803+00:00
-- url     : https://prove2.me/theorems/d0491829-6375-48de-bb79-fbe620ef9a17
-- title:
--   Minor Frame: col Sub mul
-- statement:
--   The Minor Frame construction uses the col Sub mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralDetCharacterFockColumnSubstitutionEqZero.lean#L53-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IntegralDetCharacterFockColumnSubstitutionEqZero.lean#L53-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdMinorsMemInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralDetCharacterFockColumnSubstitutionEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MeasureTheory
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
open MvPolynomial
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.colSub_mul {d a : ℕ} (A B : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    colSub (fun τ => A τ * B τ) P = colSub A (colSub B P) := by sorry
