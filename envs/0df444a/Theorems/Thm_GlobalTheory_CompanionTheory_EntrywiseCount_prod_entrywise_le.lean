-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EntrywiseCount_prod_entrywise_le
-- name    : GlobalTheory.CompanionTheory.EntrywiseCount.prod_entrywise_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:42.985097+00:00
-- url     : https://prove2.me/theorems/f5d153f6-fb66-4b4e-9dc4-e97e52f51329
-- title:
--   Entrywise Count: prod entrywise le
-- statement:
--   The Entrywise Count construction uses the prod entrywise le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdEntrywiseLe.lean#L66-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdEntrywiseLe.lean#L66-L100

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

theorem GlobalTheory.CompanionTheory.EntrywiseCount.prod_entrywise_le : ∀ (n r d : ℕ), r ≤ n → ∀ (C β t : ℝ), 0 ≤ C → 0 ≤ β → 0 ≤ t →
    ∏ i : Fin n, ∏ j : Fin n,
        C * (1 + β * (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then Real.exp t else 1)) ^ d
      ≤ C ^ (n * n) * (1 + β) ^ (d * (n * n))
        * Real.exp ((d : ℝ) * ((r : ℝ) * ((n : ℝ) - r)) * t) := by sorry
