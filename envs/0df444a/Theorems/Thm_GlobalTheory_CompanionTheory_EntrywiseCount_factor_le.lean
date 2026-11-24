-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EntrywiseCount_factor_le
-- name    : GlobalTheory.CompanionTheory.EntrywiseCount.factor_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:49.208802+00:00
-- url     : https://prove2.me/theorems/ac53ffa5-b700-44e1-b126-bf901c8bac99
-- title:
--   Entrywise Count: factor le
-- statement:
--   The Entrywise Count construction uses the factor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdEntrywiseLe.lean#L42-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdEntrywiseLe.lean#L42-L64

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProdEntrywiseLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EntrywiseCount

theorem GlobalTheory.CompanionTheory.EntrywiseCount.factor_le (d : ℕ) (C β t : ℝ) (p : Prop) [Decidable p]
    (hC : 0 ≤ C) (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    C * (1 + β * (if p then Real.exp t else 1)) ^ d
      ≤ (C * (1 + β) ^ d) * (if p then Real.exp ((d : ℝ) * t) else 1) := by sorry
