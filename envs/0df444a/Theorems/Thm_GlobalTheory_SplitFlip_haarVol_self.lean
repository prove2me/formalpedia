-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_haarVol_self
-- name    : GlobalTheory.SplitFlip.haarVol_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:51:49.494685+00:00
-- url     : https://prove2.me/theorems/b7d69f57-e133-4047-bb0b-36da6ccaa040
-- title:
--   Split Flip: haar Vol self
-- statement:
--   The Split Flip construction uses the haar Vol self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/T2SpaceGeneralLinearGroup.lean#L198-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/T2SpaceGeneralLinearGroup.lean#L198-L201

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

theorem GlobalTheory.SplitFlip.haarVol_self {J : Subgroup (GL n k)} (ho : IsOpen (J : Set (GL n k))) (hK : J ≤ KO k n) :
    haarVol J J = 1 := by sorry
