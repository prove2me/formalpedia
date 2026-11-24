-- Prove2me | Theorems.Thm_GlobalTheory_OrbitUnfold_setIntegral_pull
-- name    : GlobalTheory.OrbitUnfold.setIntegral_pull
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:38:32.067277+00:00
-- url     : https://prove2.me/theorems/2f9a7bcc-ae91-42be-aee7-f259ef92cf88
-- title:
--   Orbit Unfold: set Integral pull
-- statement:
--   The Orbit Unfold construction uses the set Integral pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TsumSetIntegralFundamentalDomainEqZeroByOrbits.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TsumSetIntegralFundamentalDomainEqZeroByOrbits.lean#L39-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TsumSetIntegralFundamentalDomainEqZeroByOrbits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal Pointwise
open GlobalTheory
open GlobalTheory.OrbitUnfold
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}

theorem GlobalTheory.OrbitUnfold.setIntegral_pull (g : H) (f : H → ℂ) :
    ∫ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 g, f (g * h) ∂ν = ∫ h in 𝓕, f h ∂ν := by sorry
