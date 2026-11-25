-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_adj_parts
-- name    : GlobalTheory.IndLine.Iwasawa.adj_parts
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:34.181654+00:00
-- url     : https://prove2.me/theorems/ed62ee76-021a-476e-b864-d287aaff77a9
-- title:
--   Iwasawa: adj parts
-- statement:
--   The Iwasawa construction uses the adj parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L154-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L154-L171

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
variable {p r q θ Z : Matrix m m ℂ}

theorem GlobalTheory.IndLine.Iwasawa.adj_parts (h : Grading p r q θ) (hp : Adj N p q) (hq : Adj N q p) (hθ : Adj N θ θ) (hZ : Adj N Z (-Z)) :
    Adj N (up p r q (Z - θ * Z * θ)) (-up p r q (Z - θ * Z * θ)) ∧ Adj N (mid p r q Z) (-mid p r q Z) ∧
      Adj N (low p r q Z + θ * low p r q Z * θ) (-(low p r q Z + θ * low p r q Z * θ)) := by sorry
