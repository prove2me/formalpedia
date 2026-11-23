-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_isLocallyConstant
-- name    : GlobalTheory.SplitWeil.HasConductor.isLocallyConstant
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:54.879136+00:00
-- url     : https://prove2.me/theorems/efa95315-f2a6-4f96-b3e9-f8d8a48ade0a
-- title:
--   Has Conductor: is Locally Constant
-- statement:
--   The Has Conductor construction uses the is Locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L293-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L293-L300

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {ψ : AddChar k Circle} {c : kˣ}

theorem GlobalTheory.SplitWeil.HasConductor.isLocallyConstant (h : HasConductor ψ c) : IsLocallyConstant ψ := by sorry
