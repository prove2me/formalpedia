-- Prove2me | Theorems.Thm_GlobalTheory_sum_piFinset_fin_succ_cons
-- name    : GlobalTheory.sum_piFinset_fin_succ_cons
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:01.789255+00:00
-- url     : https://prove2.me/theorems/439bdbc0-52d5-4749-9283-93fe0f9449e4
-- title:
--   Global Theory: sum pi Finset fin succ cons
-- statement:
--   The Global Theory construction uses the sum pi Finset fin succ cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumPiFinsetFinSuccCons.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/SumPiFinsetFinSuccCons.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumPiFinsetFinSuccCons
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset

theorem GlobalTheory.sum_piFinset_fin_succ_cons {α K : Type} [AddCommMonoid K] (n : ℕ) (S : Finset α)
    (F : (Fin (n + 1) → α) → K) :
    ∑ t ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S), F t =
      ∑ a ∈ S, ∑ t ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a t) := by sorry
