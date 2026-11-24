-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_LinAlg_exists_hasEigenvalue_ne_zero
-- name    : GlobalTheory.CompanionTheory.LinAlg.exists_hasEigenvalue_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:51:59.368803+00:00
-- url     : https://prove2.me/theorems/8f5768da-3c0b-476f-83b5-3096d59705c1
-- title:
--   Lin Alg: exists has Eigenvalue ne zero
-- statement:
--   The Lin Alg construction uses the exists has Eigenvalue ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsJointEigenvectorNonzero.lean#L61-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsJointEigenvectorNonzero.lean#L61-L83

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsJointEigenvectorNonzero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LinAlg
open Module

theorem GlobalTheory.CompanionTheory.LinAlg.exists_hasEigenvalue_ne_zero {W : Type} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (T : End ℂ W) (v : W) (m : ℕ) (hm : finrank ℂ W ≤ m)
    (hv : (T ^ m) v ≠ 0) : ∃ μ : ℂ, μ ≠ 0 ∧ T.HasEigenvalue μ := by sorry
