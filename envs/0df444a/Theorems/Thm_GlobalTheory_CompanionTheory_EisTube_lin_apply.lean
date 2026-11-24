-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_lin_apply
-- name    : GlobalTheory.CompanionTheory.EisTube.lin_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:27.261715+00:00
-- url     : https://prove2.me/theorems/dd52f0ea-d508-4446-9f63-55da30a9455e
-- title:
--   Eis Tube: lin apply
-- statement:
--   The Eis Tube construction uses the lin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IntegrableExpNegSumAbs.lean#L113-L115

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

theorem GlobalTheory.CompanionTheory.EisTube.lin_apply {ι : Type} [Fintype ι] (t : ι → ℝ) (z : ι → ℂ) :
    lin t z = 2 * (Real.pi : ℂ) * ∑ i, z i * t i := by sorry
