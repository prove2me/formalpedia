-- Prove2me | Theorems.Thm_GlobalTheory_HaarAlg_rho_mul_avg
-- name    : GlobalTheory.HaarAlg.rho_mul_avg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:58:28.583977+00:00
-- url     : https://prove2.me/theorems/28d46ac1-d8a4-4bac-9104-e4dc59443ffd
-- title:
--   Haar Alg: rho mul avg
-- statement:
--   The Haar Alg construction uses the rho mul avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsAlgebraicIntegral.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IsAlgebraicIntegral.lean#L47-L49

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

theorem GlobalTheory.HaarAlg.rho_mul_avg (ρ : K →* Matrix ι ι ℂ) (hρ : Continuous ρ) (h : K) : ρ h * avg κ ρ = avg κ ρ := by sorry
