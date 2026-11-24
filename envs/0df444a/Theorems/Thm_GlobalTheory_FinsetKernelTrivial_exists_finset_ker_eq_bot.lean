-- Prove2me | Theorems.Thm_GlobalTheory_FinsetKernelTrivial_exists_finset_ker_eq_bot
-- name    : GlobalTheory.FinsetKernelTrivial.exists_finset_ker_eq_bot
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:31:16.480136+00:00
-- url     : https://prove2.me/theorems/36dd9ae3-4c05-4144-83c9-1407f779f69d
-- title:
--   Finset Kernel Trivial: exists finset ker eq bot
-- statement:
--   The Finset Kernel Trivial construction uses the exists finset ker eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFinsetKerEqBot.lean#L14-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFinsetKerEqBot.lean#L14-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsFinsetKerEqBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinsetKernelTrivial
open scoped BigOperators

theorem GlobalTheory.FinsetKernelTrivial.exists_finset_ker_eq_bot {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V)
    [FiniteDimensional ℂ W] : ∃ P : Finset X, LinearMap.ker (restr V W P) = ⊥ := by sorry
