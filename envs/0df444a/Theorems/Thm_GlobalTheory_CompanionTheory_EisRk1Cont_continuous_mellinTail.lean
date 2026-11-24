-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisRk1Cont_continuous_mellinTail
-- name    : GlobalTheory.CompanionTheory.EisRk1Cont.continuous_mellinTail
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:37:07.64782+00:00
-- url     : https://prove2.me/theorems/a933dc3f-179d-4659-91dd-b9a92103f8bc
-- title:
--   Eis Rk1 Cont: continuous mellin Tail
-- statement:
--   The Eis Rk1 Cont construction uses the continuous mellin Tail property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSetIntegralIoiOne.lean#L83-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousSetIntegralIoiOne.lean#L83-L119

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

theorem GlobalTheory.CompanionTheory.EisRk1Cont.continuous_mellinTail {X : Type*} [TopologicalSpace X] (φ : X → ℝ → ℂ)
    (hφ : ContinuousOn (fun q : X × ℝ ↦ φ q.1 q.2) (univ ×ˢ Ioi 0))
    (hb : ∀ p₀ : X, ∀ r : ℝ, ∃ U ∈ 𝓝 p₀, ∃ M : ℝ, ∀ p ∈ U, ∀ x : ℝ, 1 ≤ x →
      ‖φ p x‖ ≤ M * x ^ (-r)) :
    Continuous fun q : ℂ × X ↦ ∫ x in Ioi (1 : ℝ), (x : ℂ) ^ (q.1 - 1) * φ q.2 x := by sorry
