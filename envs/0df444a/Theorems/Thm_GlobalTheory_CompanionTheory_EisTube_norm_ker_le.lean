-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_norm_ker_le
-- name    : GlobalTheory.CompanionTheory.EisTube.norm_ker_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:36:58.323946+00:00
-- url     : https://prove2.me/theorems/a1c466a5-802d-4078-b250-911bf6c43fce
-- title:
--   Eis Tube: norm ker le
-- statement:
--   The Eis Tube construction uses the norm ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L55-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L55-L70

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IntegrableExpNegSumAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube

theorem GlobalTheory.CompanionTheory.EisTube.norm_ker_le {ι : Type} [Fintype ι] {z : ι → ℂ} {B : ℝ} (hz : ∀ i, |(z i).re| ≤ B)
    (t : ι → ℝ) : ‖ker z t‖ ≤ Real.exp (2 * Real.pi * (B * ∑ i, |t i|)) := by sorry
