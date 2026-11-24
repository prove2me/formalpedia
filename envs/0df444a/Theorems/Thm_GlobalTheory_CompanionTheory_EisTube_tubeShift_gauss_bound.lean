-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_tubeShift_gauss_bound
-- name    : GlobalTheory.CompanionTheory.EisTube.tubeShift_gauss_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:18.280923+00:00
-- url     : https://prove2.me/theorems/c5b0a89b-3139-400a-93fb-e0afdc7224cc
-- title:
--   Eis Tube: tube Shift gauss bound
-- statement:
--   The Eis Tube construction uses the tube Shift gauss bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftTubeDomain.lean#L18-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContourShiftTubeDomain.lean#L18-L31

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

theorem GlobalTheory.CompanionTheory.EisTube.tubeShift_gauss_bound {ι : Type} [Fintype ι] (y v : ι → ℝ) (s T : ℝ) (hs : |s| ≤ T) :
    Real.exp (-(∑ i, (y i + s * v i) ^ 2) / 2) ≤
      Real.exp (T ^ 2 * (∑ i, v i ^ 2) / 2) * Real.exp (-(∑ i, y i ^ 2) / 4) := by sorry
