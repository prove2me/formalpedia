-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Hyp_adj_pq
-- name    : GlobalTheory.IndLine.Iwasawa.Hyp.adj_pq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:34.41345+00:00
-- url     : https://prove2.me/theorems/bffa61a9-199b-5f57-9e56-0817089823d5
-- title:
--   Hyp: adj pq
-- statement:
--   The Hyp construction uses the adj pq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L294-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L294-L300

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
variable {A A' : Type} [CommRing A] [CommRing A'] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable {c : A →+* A} {c' : A' →+* A'} {J : Matrix m m A} {x y : m → A} {ι : Matrix m n A} {ι' : Matrix n m A}
open GlobalTheory.IndLine.Iwasawa.Hyp
variable (h : Hyp c J x y ι ι')
include h

theorem GlobalTheory.IndLine.Iwasawa.Hyp.adj_pq : (prX c J x y)ᵀ * J = J * (prY c J x y).map c := by sorry
