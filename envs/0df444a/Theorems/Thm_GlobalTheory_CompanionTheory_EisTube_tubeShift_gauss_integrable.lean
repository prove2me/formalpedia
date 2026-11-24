-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift_gauss_integrable
-- name    : GlobalTheory.CompanionTheory.EisTube.tubeShift_gauss_integrable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:11.41848+00:00
-- url     : https://prove2.me/theorems/8f20974c-efe5-453b-8e1c-16938db50aa7
-- title:
--   Eis Tube: tube Shift gauss integrable
-- statement:
--   The Eis Tube construction uses the tube Shift gauss integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftTubeDomain.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftTubeDomain.lean#L7-L16

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

theorem GlobalTheory.CompanionTheory.EisTube.tubeShift_gauss_integrable (ι : Type) [Fintype ι] :
    Integrable (fun y : ι → ℝ => Real.exp (-(∑ i, y i ^ 2) / 4)) := by sorry
