-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_continuous_ker_left
-- name    : GlobalTheory.CompanionTheory.EisTube.continuous_ker_left
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:36:24.023171+00:00
-- url     : https://prove2.me/theorems/173ad63e-5003-45dc-85b1-67fbb3ddc368
-- title:
--   Eis Tube: continuous ker left
-- statement:
--   The Eis Tube construction uses the continuous ker left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L92-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L92-L95

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

theorem GlobalTheory.CompanionTheory.EisTube.continuous_ker_left {ι : Type} [Fintype ι] (t : ι → ℝ) :
    Continuous (fun z : ι → ℂ => ker z t) := by sorry
