-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Adj_sub
-- name    : GlobalTheory.IndLine.Iwasawa.Adj.sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:12:43.686506+00:00
-- url     : https://prove2.me/theorems/4757aad4-e6f1-497d-ac7f-d4f00958df95
-- title:
--   Adj: sub
-- statement:
--   The Adj construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L146-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L146-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {m : Type} [Fintype m] [DecidableEq m]
variable {N A B A' B' : Matrix m m ℂ}

theorem GlobalTheory.IndLine.Iwasawa.Adj.sub (h : Adj N A B) (h' : Adj N A' B') : Adj N (A - A') (B - B') := by sorry
