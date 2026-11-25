-- Prove2me | Theorems.Thm_GlobalTheory_IndLine_Iwasawa_Hyp_levi_y
-- name    : GlobalTheory.IndLine.Iwasawa.Hyp.levi_y
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:07:26.254823+00:00
-- url     : https://prove2.me/theorems/88e5d4dd-254f-58e3-96f6-604621b518bb
-- title:
--   Hyp: levi y
-- statement:
--   The Hyp construction uses the levi y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L332-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MapStarMul.lean#L332-L346

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

theorem GlobalTheory.IndLine.Iwasawa.Hyp.levi_y {g : Matrix m m A} (hq : g * prY c J x y = prY c J x y * g)
    (hu : gᵀ * J * g.map c = J) {t : Aˣ} (ht : (t : A) = (g *ᵥ x) ⬝ᵥ J *ᵥ (c ∘ y)) : g *ᵥ y = c (t⁻¹).1 • y := by sorry
