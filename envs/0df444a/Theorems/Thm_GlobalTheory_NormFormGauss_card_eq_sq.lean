-- Prove2me | Theorems.Thm_GlobalTheory_NormFormGauss_card_eq_sq
-- name    : GlobalTheory.NormFormGauss.card_eq_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:36:25.966448+00:00
-- url     : https://prove2.me/theorems/abfde073-4c30-493c-a802-dbd5812cca99
-- title:
--   Norm Form Gauss: card eq sq
-- statement:
--   The Norm Form Gauss construction uses the card eq sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumEqZeroAddUnits.lean#L8-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SumEqZeroAddUnits.lean#L8-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumEqZeroAddUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.NormFormGauss

theorem GlobalTheory.NormFormGauss.card_eq_sq {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ x, s (s x) = x)
    (r : k) (hr : s r - r ≠ 0) :
    Fintype.card k = (Finset.univ.filter (fun x : k => s x = x)).card ^ 2 := by sorry
