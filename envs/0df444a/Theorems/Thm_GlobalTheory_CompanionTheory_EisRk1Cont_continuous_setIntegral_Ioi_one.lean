-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisRk1Cont_continuous_setIntegral_Ioi_one
-- name    : GlobalTheory.CompanionTheory.EisRk1Cont.continuous_setIntegral_Ioi_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:04.376171+00:00
-- url     : https://prove2.me/theorems/730d2572-acd1-4213-8909-2b506e6cad4b
-- title:
--   Eis Rk1 Cont: continuous set Integral Ioi one
-- statement:
--   The Eis Rk1 Cont construction uses the continuous set Integral Ioi one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSetIntegralIoiOne.lean#L7-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSetIntegralIoiOne.lean#L7-L81

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousSetIntegralIoiOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisRk1Cont

theorem GlobalTheory.CompanionTheory.EisRk1Cont.continuous_setIntegral_Ioi_one {Z : Type*} [TopologicalSpace Z] (F : Z → ℝ → ℂ)
    (hF : ∀ z y, 1 ≤ y → ContinuousAt (fun w : Z × ℝ ↦ F w.1 w.2) (z, y))
    (hb : ∀ z₀, ∃ V ∈ 𝓝 z₀, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ V, ∀ x : ℝ, 1 ≤ x → ‖F z x‖ ≤ M * x ^ (-3 : ℝ)) :
    Continuous fun z ↦ ∫ x in Ioi (1 : ℝ), F z x := by sorry
