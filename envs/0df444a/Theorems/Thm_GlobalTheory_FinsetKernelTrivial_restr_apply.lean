-- Prove2me | Theorems.Thm_GlobalTheory_FinsetKernelTrivial_restr_apply
-- name    : GlobalTheory.FinsetKernelTrivial.restr_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:37.610873+00:00
-- url     : https://prove2.me/theorems/50a6202b-d39d-4072-b485-e2b1b2dc9a44
-- title:
--   Finset Kernel Trivial: restr apply
-- statement:
--   The Finset Kernel Trivial construction uses the restr apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFinsetKerEqBot.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsFinsetKerEqBot.lean#L11-L12

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

theorem GlobalTheory.FinsetKernelTrivial.restr_apply {X : Type} (V : Submodule ℂ (X → ℂ)) (W : Submodule ℂ V) (P : Finset X)
    (w : W) (x : P) : restr V W P w x = ((w : V) : X → ℂ) x := by sorry
