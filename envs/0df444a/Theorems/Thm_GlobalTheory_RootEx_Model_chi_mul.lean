-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Model_chi_mul
-- name    : GlobalTheory.RootEx.Model.chi_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:56.315656+00:00
-- url     : https://prove2.me/theorems/c221bca9-c81d-4902-ac9d-0c9852d294b5
-- title:
--   Model: chi mul
-- statement:
--   The Model construction uses the chi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L240-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L240-L245

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RootEx.Model.chi_mul (ψ : AddChar k Circle) (p : ℕ) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (h) :
    chi ψ p (u * h) = (ψ (simpleSum u) : ℂ) * chi ψ p h := by sorry
