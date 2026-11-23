-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Model_conj_mem
-- name    : GlobalTheory.RootEx.Model.conj_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:55.674024+00:00
-- url     : https://prove2.me/theorems/af15b87f-8598-481f-8934-765c1e720f10
-- title:
--   Model: conj mem
-- statement:
--   The Model construction uses the conj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L95-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L95-L115

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

theorem GlobalTheory.RootEx.Model.conj_mem {p : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) (g : GL n k) :
    (embX c g)⁻¹ * u * embX c g ∈ N k n c p := by sorry
