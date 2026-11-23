-- Prove2me | Theorems.Thm_GlobalTheory_SplitWeil_om_mul
-- name    : GlobalTheory.SplitWeil.om_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:36.981859+00:00
-- url     : https://prove2.me/theorems/1d893b93-abec-407f-a825-5016697e9a3c
-- title:
--   Split Weil: om mul
-- statement:
--   The Split Weil construction uses the om mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L194-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PadicIsNonarchimedeanLocalField.lean#L194-L199

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
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)

theorem GlobalTheory.SplitWeil.om_mul (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ) :
    om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ) := by sorry
