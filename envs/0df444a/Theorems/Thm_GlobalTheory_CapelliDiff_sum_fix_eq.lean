-- Prove2me | Theorems.Thm_GlobalTheory_CapelliDiff_sum_fix_eq
-- name    : GlobalTheory.CapelliDiff.sum_fix_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:32.210728+00:00
-- url     : https://prove2.me/theorems/75878973-0ff8-40c6-83c6-8de5e3bf370f
-- title:
--   Capelli Diff: sum fix eq
-- statement:
--   The Capelli Diff construction uses the sum fix eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QdetAddOneSubEqSumQminor.lean#L59-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QdetAddOneSubEqSumQminor.lean#L59-L73

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

theorem GlobalTheory.CapelliDiff.sum_fix_eq {A : Type*} [AddCommMonoid A] {m : ℕ} (k : Fin (m + 1))
    (g : Equiv.Perm (Fin (m + 1)) → A) :
    ∑ σ : Equiv.Perm (Fin (m + 1)), (if σ k = k then g σ else 0) =
      ∑ τ : Equiv.Perm (Fin m), g (extAt k τ) := by sorry
