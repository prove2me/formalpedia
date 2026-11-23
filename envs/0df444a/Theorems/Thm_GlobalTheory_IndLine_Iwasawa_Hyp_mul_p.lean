-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Hyp_mul_p
-- name    : GlobalTheory.IndLine.Iwasawa.Hyp.mul_p
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:22.516406+00:00
-- url     : https://prove2.me/theorems/4589d2e5-81e6-4de9-aad5-445374808649
-- title:
--   Hyp: mul p
-- statement:
--   The Hyp construction uses the mul p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L277-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L277-L278

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
omit h

theorem GlobalTheory.IndLine.Iwasawa.Hyp.mul_p (g : Matrix m m A) : g * prX c J x y = Matrix.vecMulVec (g *ᵥ x) (J *ᵥ (c ∘ y)) := by sorry
