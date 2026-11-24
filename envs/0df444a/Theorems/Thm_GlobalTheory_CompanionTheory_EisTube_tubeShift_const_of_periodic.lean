-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift_const_of_periodic
-- name    : GlobalTheory.CompanionTheory.EisTube.tubeShift_const_of_periodic
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:13.516797+00:00
-- url     : https://prove2.me/theorems/dd155c99-d19b-4812-8262-6cc78310ef3d
-- title:
--   Eis Tube: tube Shift const of periodic
-- statement:
--   The Eis Tube construction uses the tube Shift const of periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftTubeDomain.lean#L94-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftTubeDomain.lean#L94-L112

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContourShiftTubeDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube

theorem GlobalTheory.CompanionTheory.EisTube.tubeShift_const_of_periodic (U : Set ℂ) (hU : IsOpen U) (hc : IsPreconnected U)
    (Φ : ℂ → ℂ) (hd : DifferentiableOn ℂ Φ U)
    (hper : ∀ w ∈ U, ∀ s : ℝ, Φ (w + (s : ℂ) * Complex.I) = Φ w)
    {a b : ℂ} (ha : a ∈ U) (hb : b ∈ U) : Φ a = Φ b := by sorry
