-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WeilSiegel_NoFrame_isOpen_posOn
-- name    : GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:55.923869+00:00
-- url     : https://prove2.me/theorems/b0d1f666-ed6a-4729-aaf9-d10adf06da8d
-- title:
--   No Frame: is Open pos On
-- statement:
--   The No Frame construction uses the is Open pos On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PositiveOnSubspaceOpen.lean#L8-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PositiveOnSubspaceOpen.lean#L8-L41

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableOfMulUnimodular
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PositiveOnSubspaceOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WeilSiegel GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.isOpen_posOn (n : ℕ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)) :
    IsOpen {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} := by sorry
