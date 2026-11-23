-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_Model_coord_embedding
-- name    : GlobalTheory.RootEx.Model.coord_embedding
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:59.173548+00:00
-- url     : https://prove2.me/theorems/a626806c-9efc-4d83-bb0e-3b371946a9d5
-- title:
--   Model: coord embedding
-- statement:
--   The Model construction uses the coord embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L187-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/SimpleSumRowCol.lean#L187-L220

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
variable [MeasurableSpace k]

theorem GlobalTheory.RootEx.Model.coord_embedding (p : ℕ) : MeasurableEmbedding
    (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) ∧ Function.Surjective
    (fun (g : N k n c p) (rs : {rs : (n ⊕ Fin c) × (n ⊕ Fin c) // lev p rs.1 < lev p rs.2}) =>
      (g : GL (n ⊕ Fin c) k).val rs.1.1 rs.1.2) := by sorry
