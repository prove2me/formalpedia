-- Prove2me | Theorems.Thm_GlobalTheory_FinsetKernelTrivial_main
-- name    : GlobalTheory.FinsetKernelTrivial.main
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:04:59.953913+00:00
-- url     : https://prove2.me/theorems/530fcf2b-5e91-539b-974d-b384665c32d2
-- title:
--   Finset Kernel Trivial: main
-- statement:
--   The Finset Kernel Trivial construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFinsetKerEqBot.lean#L46-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFinsetKerEqBot.lean#L46-L69

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

theorem GlobalTheory.FinsetKernelTrivial.main : ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ ↥V) [FiniteDimensional ℂ ↥W],
    ∃ (P : Finset X) (e : X → ↥V), ∀ w ∈ W, w = ∑ x ∈ P, (↑w : X → ℂ) x • e x := by sorry
