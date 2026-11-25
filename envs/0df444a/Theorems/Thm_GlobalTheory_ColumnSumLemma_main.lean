-- Prove2me | Theorems.Thm_GlobalTheory_ColumnSumLemma_main
-- name    : GlobalTheory.ColumnSumLemma.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:01:43.964705+00:00
-- url     : https://prove2.me/theorems/1dcde3d3-019b-585c-aff9-eabf3e9fd3be
-- title:
--   Column Sum Lemma: main
-- statement:
--   The Column Sum Lemma construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColSum.lean#L9-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ColSum.lean#L9-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ColumnSumLemma
open Matrix

theorem GlobalTheory.ColumnSumLemma.main : ∀ {A : Type} [inst : CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (I : Set (Fin r)) (y : Fin n → A), y ∈ Submodule.span A ((fun (i : Fin r) ↦ Matrix.transpose C i) '' I) ↔ ∃ (a : Fin r → A), (∀ l ∉ I, a l = (0 : A)) ∧ Matrix.mulVec C a = y := by sorry
