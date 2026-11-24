-- Prove2me | Theorems.Thm_GlobalTheory_RapidFourier_hasDerivAt_wave
-- name    : GlobalTheory.RapidFourier.hasDerivAt_wave
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:49.987355+00:00
-- url     : https://prove2.me/theorems/216fb900-258b-466c-bbe2-896bff5f04f4
-- title:
--   Rapid Fourier: has Deriv At wave
-- statement:
--   The Rapid Fourier construction uses the has Deriv At wave property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean#L29-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.RapidFourier

theorem GlobalTheory.RapidFourier.hasDerivAt_wave (a : ℂ) (t : ℝ) :
    HasDerivAt (wave a) (wave (2 * π * I * a) t) t := by sorry
