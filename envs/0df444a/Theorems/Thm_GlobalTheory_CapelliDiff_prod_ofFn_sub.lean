-- Prove2me | Theorems.Thm_GlobalTheory_CapelliDiff_prod_ofFn_sub
-- name    : GlobalTheory.CapelliDiff.prod_ofFn_sub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:09.089651+00:00
-- url     : https://prove2.me/theorems/15a79e39-3317-4843-97b2-099b21572b8b
-- title:
--   Capelli Diff: prod of Fn sub
-- statement:
--   The Capelli Diff construction uses the prod of Fn sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QdetAddOneSubEqSumQminor.lean#L7-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QdetAddOneSubEqSumQminor.lean#L7-L36

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QdetAddOneSubEqSumQminor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
open GlobalTheory GlobalTheory.CapelliDiff

theorem GlobalTheory.CapelliDiff.prod_ofFn_sub {A : Type*} [Ring A] [Algebra ℂ A] :
    ∀ (n : ℕ) (x y : Fin (n + 1) → A) (d : Fin (n + 1) → ℂ),
      (∀ k, y k = x k + algebraMap ℂ A (d k)) →
      (List.ofFn y).prod - (List.ofFn x).prod =
        ∑ k : Fin (n + 1), algebraMap ℂ A (d k) *
          (List.ofFn fun j : Fin n => if Fin.castSucc j < k then x (Fin.castSucc j) else y j.succ).prod := by sorry
