-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LocalFieldChar_isOpen_addChar_ker
-- name    : GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:51:55.554592+00:00
-- url     : https://prove2.me/theorems/9f4070a2-2f34-4986-a020-354dadbeea2f
-- title:
--   Local Field Char: is Open add Char ker
-- statement:
--   The Local Field Char construction uses the is Open add Char ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsOpenAdditiveCharacterKernel.lean#L54-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsOpenAdditiveCharacterKernel.lean#L54-L86

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenAdditiveCharacterKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalFieldChar

theorem GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ →
    IsOpen {x : k | ψ x = 1} := by sorry
