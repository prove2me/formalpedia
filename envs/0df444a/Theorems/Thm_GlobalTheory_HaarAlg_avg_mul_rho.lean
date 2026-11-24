-- Prove2me | Theorems.Thm_GlobalTheory_HaarAlg_avg_mul_rho
-- name    : GlobalTheory.HaarAlg.avg_mul_rho
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:58:35.628143+00:00
-- url     : https://prove2.me/theorems/b106ec1c-e86d-4efd-a0a1-d57d53588ea7
-- title:
--   Haar Alg: avg mul rho
-- statement:
--   The Haar Alg construction uses the avg mul rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsAlgebraicIntegral.lean#L51-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsAlgebraicIntegral.lean#L51-L62

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

theorem GlobalTheory.HaarAlg.avg_mul_rho (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : avg κ ρ * ρ h = avg κ ρ := by sorry
