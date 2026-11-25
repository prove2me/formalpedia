-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothLog_exists_smooth_log
-- name    : GlobalTheory.CompanionTheory.SmoothLog.exists_smooth_log
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:01:45.437633+00:00
-- url     : https://prove2.me/theorems/d3266097-f7f6-53f5-b430-2a6105223b23
-- title:
--   Smooth Log: exists smooth log
-- statement:
--   The Smooth Log construction uses the exists smooth log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmoothLog.lean#L31-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSmoothLog.lean#L31-L49

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

theorem GlobalTheory.CompanionTheory.SmoothLog.exists_smooth_log : ∀ (n : ℕ), ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (L : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧ ContDiffOn ℝ ∞ L U ∧ L 1 = 0 ∧ (∀ g ∈ U, NormedSpace.exp (L g) = g) ∧ (∀ᶠ X in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), L (NormedSpace.exp X) = X) ∧ ContDiff ℝ ∞ (fun X : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp X) := by sorry
