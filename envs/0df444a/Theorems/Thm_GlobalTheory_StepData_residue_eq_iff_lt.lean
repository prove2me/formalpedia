-- Prove2me | Theorems.Thm_GlobalTheory_StepData_residue_eq_iff_lt
-- name    : GlobalTheory.StepData.residue_eq_iff_lt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:38.394597+00:00
-- url     : https://prove2.me/theorems/a468be46-9df7-4247-bdd8-8e4dca0c0367
-- title:
--   Step Data: residue eq iff lt
-- statement:
--   The Step Data construction uses the residue eq iff lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ValuationDetOfMemKO.lean#L72-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k]
variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem GlobalTheory.StepData.residue_eq_iff_lt (x y : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = IsLocalRing.residue 𝒪[k] y ↔ valuation k ((x : k) - y) < 1 := by sorry
