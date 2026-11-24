-- Prove2me | Theorems.Thm_GlobalTheory_HaarAlg_avg_left
-- name    : GlobalTheory.HaarAlg.avg_left
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:58:29.138523+00:00
-- url     : https://prove2.me/theorems/ea724f12-bff4-4d91-b37a-2415246dd1b0
-- title:
--   Haar Alg: avg left
-- statement:
--   The Haar Alg construction uses the avg left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsAlgebraicIntegral.lean#L43-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsAlgebraicIntegral.lean#L43-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsAlgebraicIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory GlobalTheory.HaarAlg
variable {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (κ : Measure K) [IsProbabilityMeasure κ] {ι : Type} [Fintype ι] [DecidableEq ι]
variable [κ.IsMulLeftInvariant]
omit [CompactSpace K] [IsProbabilityMeasure κ] [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.HaarAlg.avg_left (F : K → Matrix ι ι ℂ) (h : K) : (avg κ fun g => F (h * g)) = avg κ F := by sorry
