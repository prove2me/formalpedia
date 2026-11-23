-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Adj_mul
-- name    : GlobalTheory.IndLine.Iwasawa.Adj.mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:32:45.787942+00:00
-- url     : https://prove2.me/theorems/fbeb9afd-4be4-4110-94c0-cf30fb62cb5a
-- title:
--   Adj: mul
-- statement:
--   The Adj construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L139-L141

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

theorem GlobalTheory.IndLine.Iwasawa.Adj.mul (h : Adj N A B) (h' : Adj N A' B') : Adj N (A * A') (B' * B) := by sorry
