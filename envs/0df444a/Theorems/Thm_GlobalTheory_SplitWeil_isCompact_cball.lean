-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_isCompact_cball
-- name    : GlobalTheory.SplitWeil.isCompact_cball
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:11.478457+00:00
-- url     : https://prove2.me/theorems/3ee6076d-713b-4acd-be39-1b0675c5041b
-- title:
--   Split Weil: is Compact cball
-- statement:
--   The Split Weil construction uses the is Compact cball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L91-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L91-L92

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

theorem GlobalTheory.SplitWeil.isCompact_cball (s : kˣ) : IsCompact (cball s) := by sorry
