-- Prove2me | Theorems.Thm_GlobalTheory_OrbitUnfold_aedisjoint_pull
-- name    : GlobalTheory.OrbitUnfold.aedisjoint_pull
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:37:11.368832+00:00
-- url     : https://prove2.me/theorems/b64fee26-1849-4c5d-8ce5-af6c0f2fa1a2
-- title:
--   Orbit Unfold: aedisjoint pull
-- statement:
--   The Orbit Unfold construction uses the aedisjoint pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TsumSetIntegralFundamentalDomainEqZeroByOrbits.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/TsumSetIntegralFundamentalDomainEqZeroByOrbits.lean#L26-L33

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

theorem GlobalTheory.OrbitUnfold.aedisjoint_pull (hF : IsFundamentalDomain Γ 𝓕 ν) {a b : Γ}
    (hab : a ≠ b) :
    AEDisjoint ν (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (a : H)) (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (b : H)) := by sorry
