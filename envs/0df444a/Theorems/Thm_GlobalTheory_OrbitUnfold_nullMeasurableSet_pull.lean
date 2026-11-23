-- Prove2me | Theorems.Thm_GlobalTheory_OrbitUnfold_nullMeasurableSet_pull
-- name    : GlobalTheory.OrbitUnfold.nullMeasurableSet_pull
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:49.64696+00:00
-- url     : https://prove2.me/theorems/a38382c5-7e3f-4422-b6d8-9115c6d63a84
-- title:
--   Orbit Unfold: null Measurable Set pull
-- statement:
--   The Orbit Unfold construction uses the null Measurable Set pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TsumSetIntegralFundamentalDomainEqZeroByOrbits.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TsumSetIntegralFundamentalDomainEqZeroByOrbits.lean#L18-L20

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

theorem GlobalTheory.OrbitUnfold.nullMeasurableSet_pull (hF : IsFundamentalDomain Γ 𝓕 ν) (g : H) :
    NullMeasurableSet (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 g) ν := by sorry
