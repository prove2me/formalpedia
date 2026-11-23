-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_prY_mulVec
-- name    : GlobalTheory.IndLine.Iwasawa.prY_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:48.297818+00:00
-- url     : https://prove2.me/theorems/9f4f26b1-7c70-4f12-9ea8-83ab054b5af7
-- title:
--   Iwasawa: pr Y mul Vec
-- statement:
--   The Iwasawa construction uses the pr Y mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L255-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L255-L256

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

theorem GlobalTheory.IndLine.Iwasawa.prY_mulVec (v : m → A) : prY c J x y *ᵥ v = -(v ⬝ᵥ J *ᵥ (c ∘ x)) • y := by sorry
