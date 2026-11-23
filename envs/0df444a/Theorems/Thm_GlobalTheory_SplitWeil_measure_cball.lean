-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_measure_cball
-- name    : GlobalTheory.SplitWeil.measure_cball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:26.837712+00:00
-- url     : https://prove2.me/theorems/d447394b-b50a-4d9c-b252-6264e4e29a70
-- title:
--   Split Weil: measure cball
-- statement:
--   The Split Weil construction uses the measure cball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L122-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L122-L126

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
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.SplitWeil.measure_cball (ν : Measure k) [ν.IsAddHaarMeasure] (s : kˣ) :
    ν (cball s) = distribHaarChar k s * ν (𝒪[k] : Set k) := by sorry
