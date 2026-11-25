-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Hyp_adj_qp
-- name    : GlobalTheory.IndLine.Iwasawa.Hyp.adj_qp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:39.993327+00:00
-- url     : https://prove2.me/theorems/99381b10-90a6-5ada-98bd-0d8af529cf76
-- title:
--   Hyp: adj qp
-- statement:
--   The Hyp construction uses the adj qp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L302-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L302-L309

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

theorem GlobalTheory.IndLine.Iwasawa.Hyp.adj_qp : (prY c J x y)ᵀ * J = J * (prX c J x y).map c := by sorry
