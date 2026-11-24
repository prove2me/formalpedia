-- Prove2me | Theorems.Thm_GlobalTheory_StdLoc_mem_blockPar
-- name    : GlobalTheory.StdLoc.mem_blockPar
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:12:18.419973+00:00
-- url     : https://prove2.me/theorems/ca9049f0-6fd6-4298-b032-da24821f646e
-- title:
--   Std Loc: mem block Par
-- statement:
--   The Std Loc construction uses the mem block Par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RowBlockIndicatorFromLtIff.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RowBlockIndicatorFromLtIff.lean#L23-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.StdLoc

theorem GlobalTheory.StdLoc.mem_blockPar {R : Type} [CommRing R] {a d : ℕ} (g : GL (Fin d) R) :
    g ∈ _root_.GlobalTheory.StdLoc.blockPar R a d ↔ ∀ i j : Fin d, j.1 < a → a ≤ i.1 → (g : Matrix (Fin d) (Fin d) R) i j = 0 := by sorry
