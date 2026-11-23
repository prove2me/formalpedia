-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_exists_ne_one
-- name    : GlobalTheory.SplitWeil.HasConductor.exists_ne_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:55.441786+00:00
-- url     : https://prove2.me/theorems/0ecdede0-1957-42da-a3b7-6902d28f0c04
-- title:
--   Has Conductor: exists ne one
-- statement:
--   The Has Conductor construction uses the exists ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L304-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L304-L319

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

theorem GlobalTheory.SplitWeil.HasConductor.exists_ne_one (h : HasConductor ψ c) (s : kˣ) {x : k} (hx : x ∉ cball (c * s⁻¹)) :
    ∃ t ∈ cball s, ψ (t * x) ≠ 1 := by sorry
