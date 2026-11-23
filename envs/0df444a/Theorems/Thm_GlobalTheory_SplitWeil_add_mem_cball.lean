-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
-- name    : GlobalTheory.SplitWeil.add_mem_cball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:14:49.139581+00:00
-- url     : https://prove2.me/theorems/6b459a00-5879-4391-b82d-31ce36e3a23a
-- title:
--   Split Weil: add mem cball
-- statement:
--   The Split Weil construction uses the add mem cball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L321-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L321-L323

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

theorem GlobalTheory.SplitWeil.add_mem_cball {s : kˣ} {x y : k} (hx : x ∈ cball s) (hy : y ∈ cball s) : x + y ∈ cball s := by sorry
