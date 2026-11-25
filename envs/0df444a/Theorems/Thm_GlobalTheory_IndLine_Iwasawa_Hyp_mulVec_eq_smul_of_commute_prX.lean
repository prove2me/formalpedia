-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Hyp_mulVec_eq_smul_of_commute_prX
-- name    : GlobalTheory.IndLine.Iwasawa.Hyp.mulVec_eq_smul_of_commute_prX
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:31.855559+00:00
-- url     : https://prove2.me/theorems/9b5e8e4b-5f84-5c2f-b8e7-0b8cc23643a6
-- title:
--   Hyp: mul Vec eq smul of commute pr X
-- statement:
--   The Hyp construction uses the mul Vec eq smul of commute pr X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L328-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L328-L330

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

theorem GlobalTheory.IndLine.Iwasawa.Hyp.mulVec_eq_smul_of_commute_prX {g : Matrix m m A} (hg : g * prX c J x y = prX c J x y * g) :
    g *ᵥ x = ((g *ᵥ x) ⬝ᵥ J *ᵥ (c ∘ y)) • x := by sorry
