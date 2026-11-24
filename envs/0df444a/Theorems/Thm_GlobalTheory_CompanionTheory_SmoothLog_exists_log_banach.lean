-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothLog_exists_log_banach
-- name    : GlobalTheory.CompanionTheory.SmoothLog.exists_log_banach
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:15:57.211838+00:00
-- url     : https://prove2.me/theorems/51c8c2f6-d4c6-49d9-9fd7-5b3a9164fab8
-- title:
--   Smooth Log: exists log banach
-- statement:
--   The Smooth Log construction uses the exists log banach property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmoothLog.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmoothLog.lean#L9-L18

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SmComplete
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_ContDiffOnExpPartialHomeomorphSymm
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSmoothLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open SmoothVectors Filter Topology
open scoped ContDiff Matrix.Norms.Elementwise
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothLog

theorem GlobalTheory.CompanionTheory.SmoothLog.exists_log_banach (A : Type*) [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] :
    ∃ (U : Set A) (L : A → A), IsOpen U ∧ (1 : A) ∈ U ∧ ContDiffOn ℝ ∞ L U ∧ L 1 = 0 ∧
      (∀ g ∈ U, NormedSpace.exp (L g) = g) ∧
      (∀ᶠ X in 𝓝 (0 : A), L (NormedSpace.exp X) = X) := by sorry
