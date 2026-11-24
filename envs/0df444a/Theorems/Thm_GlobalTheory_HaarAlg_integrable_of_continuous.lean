-- Prove2me | Theorems.Thm_GlobalTheory_HaarAlg_integrable_of_continuous
-- name    : GlobalTheory.HaarAlg.integrable_of_continuous
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:58:27.332839+00:00
-- url     : https://prove2.me/theorems/b1d070bc-db10-49e7-8d31-3a0b6d252878
-- title:
--   Haar Alg: integrable of continuous
-- statement:
--   The Haar Alg construction uses the integrable of continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsAlgebraicIntegral.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsAlgebraicIntegral.lean#L12-L13

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
omit [Group K] [IsTopologicalGroup K]

theorem GlobalTheory.HaarAlg.integrable_of_continuous {f : K → ℂ} (hf : Continuous f) : Integrable f κ := by sorry
