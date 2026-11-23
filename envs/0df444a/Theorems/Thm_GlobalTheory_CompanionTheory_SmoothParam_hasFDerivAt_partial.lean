-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_hasFDerivAt_partial
-- name    : GlobalTheory.CompanionTheory.SmoothParam.hasFDerivAt_partial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:23.910004+00:00
-- url     : https://prove2.me/theorems/78a2d92f-dd94-4570-9ea2-668a5fd816f4
-- title:
--   Smooth Param: has FDeriv At partial
-- statement:
--   The Smooth Param construction uses the has FDeriv At partial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean#L16-L19

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContDiffIntegralDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothParam
variable {Ω P Y F : Type} [MeasurableSpace Ω] [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ Y]

theorem GlobalTheory.CompanionTheory.SmoothParam.hasFDerivAt_partial {H : P × Y → F} (hH : Differentiable ℝ H) (p : P) (y : Y) :
    HasFDerivAt (fun q => H (q, y))
      ((fderiv ℝ H (p, y)).comp (ContinuousLinearMap.inl ℝ P Y)) p := by sorry
