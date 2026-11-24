-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EntrywiseCount_prod_indicator
-- name    : GlobalTheory.CompanionTheory.EntrywiseCount.prod_indicator
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:37:02.644988+00:00
-- url     : https://prove2.me/theorems/67d7c8fe-183e-4fda-864e-9bbaa3d38f1e
-- title:
--   Entrywise Count: prod indicator
-- statement:
--   The Entrywise Count construction uses the prod indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdEntrywiseLe.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProdEntrywiseLe.lean#L28-L40

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

theorem GlobalTheory.CompanionTheory.EntrywiseCount.prod_indicator (n r : ℕ) (hr : r ≤ n) (E : ℝ) :
    ∏ i : Fin n, ∏ j : Fin n, (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then E else 1)
      = E ^ (r * (n - r)) := by sorry
