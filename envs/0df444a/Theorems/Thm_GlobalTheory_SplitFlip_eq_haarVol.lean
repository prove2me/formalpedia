-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_eq_haarVol
-- name    : GlobalTheory.SplitFlip.eq_haarVol
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:20:02.311639+00:00
-- url     : https://prove2.me/theorems/72bf51a4-c44c-4e31-b30d-7498c65f177b
-- title:
--   Split Flip: eq haar Vol
-- statement:
--   The Split Flip construction uses the eq haar Vol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/T2SpaceGeneralLinearGroup.lean#L203-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/T2SpaceGeneralLinearGroup.lean#L203-L209

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SplitFlip.eq_haarVol (μ : Measure (GL n k)) [μ.IsHaarMeasure] {J : Subgroup (GL n k)}
    (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) (h1 : μ J = 1) : μ = haarVol J := by sorry
