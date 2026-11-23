-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_prX_mulVec
-- name    : GlobalTheory.IndLine.Iwasawa.prX_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:55.99444+00:00
-- url     : https://prove2.me/theorems/88700e68-c8e6-4bc6-8f55-096c0d6d06b9
-- title:
--   Iwasawa: pr X mul Vec
-- statement:
--   The Iwasawa construction uses the pr X mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L252-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L252-L253

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

theorem GlobalTheory.IndLine.Iwasawa.prX_mulVec (v : m → A) : prX c J x y *ᵥ v = (v ⬝ᵥ J *ᵥ (c ∘ y)) • x := by sorry
