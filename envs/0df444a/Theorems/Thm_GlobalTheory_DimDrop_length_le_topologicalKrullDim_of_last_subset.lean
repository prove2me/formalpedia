-- Prove2me | Theorems.Thm_GlobalTheory_DimDrop_length_le_topologicalKrullDim_of_last_subset
-- name    : GlobalTheory.DimDrop.length_le_topologicalKrullDim_of_last_subset
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:48:55.83387+00:00
-- url     : https://prove2.me/theorems/c9dccd63-5caf-4efc-8c92-084f0f5daa3a
-- title:
--   Dim Drop: length le topological Krull Dim of last subset
-- statement:
--   The Dim Drop construction uses the length le topological Krull Dim of last subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimDropAndFiniteOfDimZero.lean#L7-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimDropAndFiniteOfDimZero.lean#L7-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimDropAndFiniteOfDimZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TopologicalSpace Order
open GlobalTheory GlobalTheory.DimDrop

theorem GlobalTheory.DimDrop.length_le_topologicalKrullDim_of_last_subset {X : Type} [TopologicalSpace X] (Z : Set X)
    (q : LTSeries (IrreducibleCloseds X)) (h : (q.last : Set X) ⊆ Z) :
    (q.length : WithBot ℕ∞) ≤ topologicalKrullDim Z := by sorry
