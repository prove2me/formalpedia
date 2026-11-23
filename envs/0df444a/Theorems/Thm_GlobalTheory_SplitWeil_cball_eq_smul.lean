-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_cball_eq_smul
-- name    : GlobalTheory.SplitWeil.cball_eq_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:09.005328+00:00
-- url     : https://prove2.me/theorems/9f4bbd07-ce0a-4a7d-866a-f44b76120457
-- title:
--   Split Weil: cball eq smul
-- statement:
--   The Split Weil construction uses the cball eq smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L81-L86

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

theorem GlobalTheory.SplitWeil.cball_eq_smul (s : kˣ) : cball s = s • (𝒪[k] : Set k) := by sorry
