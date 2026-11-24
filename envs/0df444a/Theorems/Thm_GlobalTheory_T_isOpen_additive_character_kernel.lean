-- Prove2me | Theorems.Thm_GlobalTheory_T_isOpen_additive_character_kernel
-- name    : GlobalTheory.T.isOpen_additive_character_kernel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:49:27.62096+00:00
-- url     : https://prove2.me/theorems/6a2912b1-f390-4336-9a5c-e40440855a5d
-- title:
--   T: is Open additive character kernel
-- statement:
--   The T construction uses the is Open additive character kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsOpenAdditiveCharacterKernelStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsOpenAdditiveCharacterKernelStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenAdditiveCharacterKernel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsOpenAdditiveCharacterKernelStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isOpen_additive_character_kernel : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → IsOpen {x : k | ψ x = 1} := by sorry
