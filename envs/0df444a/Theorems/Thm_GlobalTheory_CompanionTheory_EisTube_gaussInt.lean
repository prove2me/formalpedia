-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EisTube_gaussInt
-- name    : GlobalTheory.CompanionTheory.EisTube.gaussInt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:12:12.254192+00:00
-- url     : https://prove2.me/theorems/67c40800-1868-4875-88bb-b2964a2a8eb0
-- title:
--   Eis Tube: gauss Int
-- statement:
--   The Eis Tube construction uses the gauss Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianIntegrableFiniteDim.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/GaussianIntegrableFiniteDim.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_GaussianIntegrableFiniteDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EisTube

theorem GlobalTheory.CompanionTheory.EisTube.gaussInt : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c →
    MeasureTheory.Integrable (fun y : ι → ℝ => Real.exp (-(c * ∑ i, y i ^ 2))) := by sorry
