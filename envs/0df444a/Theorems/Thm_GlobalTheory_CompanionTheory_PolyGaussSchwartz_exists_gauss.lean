-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PolyGaussSchwartz_exists_gauss
-- name    : GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_gauss
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:54:48.319863+00:00
-- url     : https://prove2.me/theorems/7749ba50-be6a-463f-a56f-7140e09ba9f5
-- title:
--   Poly Gauss Schwartz: exists gauss
-- statement:
--   The Poly Gauss Schwartz construction uses the exists gauss property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzPolyMulGauss.lean#L58-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsSchwartzPolyMulGauss.lean#L58-L66

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianSchwartz
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsSchwartzPolyMulGauss
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PolyGaussSchwartz
variable {m n : ℕ}

theorem GlobalTheory.CompanionTheory.PolyGaussSchwartz.exists_gauss : ∃ g : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u,
    g u = Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) := by sorry
