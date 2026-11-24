-- Prove2me | Theorems.Thm_GlobalTheory_ColumnSumLemma_colSum
-- name    : GlobalTheory.ColumnSumLemma.colSum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:14:58.282217+00:00
-- url     : https://prove2.me/theorems/3f07832b-cf53-4bd5-8f8c-ef7042b92ab9
-- title:
--   Column Sum Lemma: col Sum
-- statement:
--   The Column Sum Lemma construction uses the col Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColSum.lean#L4-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColSum.lean#L4-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ColumnSumLemma
open Matrix

theorem GlobalTheory.ColumnSumLemma.colSum {A : Type} [CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (a : Fin r → A) :
    Matrix.mulVec C a = ∑ i, a i • Matrix.transpose C i := by sorry
