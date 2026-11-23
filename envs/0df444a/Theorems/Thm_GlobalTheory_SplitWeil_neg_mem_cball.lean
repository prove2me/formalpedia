-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball
-- name    : GlobalTheory.SplitWeil.neg_mem_cball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:11.460797+00:00
-- url     : https://prove2.me/theorems/63849b13-40de-4416-9fa8-dcf01fb8e01f
-- title:
--   Split Weil: neg mem cball
-- statement:
--   The Split Weil construction uses the neg mem cball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L325-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L325-L326

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

theorem GlobalTheory.SplitWeil.neg_mem_cball {s : kˣ} {x : k} (hx : x ∈ cball s) : -x ∈ cball s := by sorry
