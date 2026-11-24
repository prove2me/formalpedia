-- Prove2me | Theorems.Thm_GlobalTheory_StdLoc_card_blockPar
-- name    : GlobalTheory.StdLoc.card_blockPar
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:12.853301+00:00
-- url     : https://prove2.me/theorems/e6780900-138f-46d4-bf5f-716151838be9
-- title:
--   Std Loc: card block Par
-- statement:
--   The Std Loc construction uses the card block Par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardBlockParabolicSubgroupGL.lean#L63-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardBlockParabolicSubgroupGL.lean#L63-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RowBlockIndicatorFromLtIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardBlockParabolicSubgroupGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField UniqueFactorizationMonoid GlobalTheory.StdLoc
noncomputable section
open GlobalTheory GlobalTheory.StdLoc

theorem GlobalTheory.StdLoc.card_blockPar (R : Type) [CommRing R] [Finite R] (a d : ℕ) (h : a ≤ d) :
    Nat.card (blockPar R a d) =
      Nat.card (GL (Fin a) R) * Nat.card (GL (Fin (d - a)) R) * Nat.card R ^ (a * (d - a)) := by sorry
