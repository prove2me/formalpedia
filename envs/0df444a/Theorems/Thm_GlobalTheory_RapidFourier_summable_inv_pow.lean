-- Prove2me | Theorems.Thm_GlobalTheory_RapidFourier_summable_inv_pow
-- name    : GlobalTheory.RapidFourier.summable_inv_pow
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:14:01.775231+00:00
-- url     : https://prove2.me/theorems/fb20ecc3-008b-4b83-852e-8a75d1c63a3f
-- title:
--   Rapid Fourier: summable inv pow
-- statement:
--   The Rapid Fourier construction uses the summable inv pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean#L93-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean#L93-L107

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

theorem GlobalTheory.RapidFourier.summable_inv_pow (n : ℕ) :
    Summable fun ν : Fin n → ℤ => ((1 + ∑ k, |(ν k : ℝ)|) ^ (2 * n))⁻¹ := by sorry
