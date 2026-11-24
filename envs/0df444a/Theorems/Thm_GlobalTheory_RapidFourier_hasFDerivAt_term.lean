-- Prove2me | Theorems.Thm_GlobalTheory_RapidFourier_hasFDerivAt_term
-- name    : GlobalTheory.RapidFourier.hasFDerivAt_term
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:03.638715+00:00
-- url     : https://prove2.me/theorems/3474bfea-d4ee-4818-8b06-d0c88fd1874b
-- title:
--   Rapid Fourier: has FDeriv At term
-- statement:
--   The Rapid Fourier construction uses the has FDeriv At term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean#L119-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean#L119-L124

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

theorem GlobalTheory.RapidFourier.hasFDerivAt_term {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    HasFDerivAt (wave a ∘ linForm ν)
      ((linForm ν).smulRight (wave (2 * π * I * a) (linForm ν x))) x := by sorry
