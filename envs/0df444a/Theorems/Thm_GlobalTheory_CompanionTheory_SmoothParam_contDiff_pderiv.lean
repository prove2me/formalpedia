-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothParam_contDiff_pderiv
-- name    : GlobalTheory.CompanionTheory.SmoothParam.contDiff_pderiv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:24.968901+00:00
-- url     : https://prove2.me/theorems/aff48fdd-f1da-4b9a-83b1-39e802b7ce97
-- title:
--   Smooth Param: cont Diff pderiv
-- statement:
--   The Smooth Param construction uses the cont Diff pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContDiffIntegralDensity.lean#L28-L31

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

theorem GlobalTheory.CompanionTheory.SmoothParam.contDiff_pderiv {H : P × Y → F} (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ (pderiv H) := by sorry
