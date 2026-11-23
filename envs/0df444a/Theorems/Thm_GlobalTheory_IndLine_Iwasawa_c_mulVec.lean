-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_c_mulVec
-- name    : GlobalTheory.IndLine.Iwasawa.c_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:17.00586+00:00
-- url     : https://prove2.me/theorems/54b6d654-eeba-40ff-b47f-2d0fc607b3dc
-- title:
--   Iwasawa: c mul Vec
-- statement:
--   The Iwasawa construction uses the c mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L258-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L258-L262

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

theorem GlobalTheory.IndLine.Iwasawa.c_mulVec (cc : ∀ a, c (c a) = a) (skew : J.map c = -Jᵀ) (v : m → A) : c ∘ (J *ᵥ (c ∘ v)) = -(v ᵥ* J) := by sorry
