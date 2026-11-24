-- Prove2me | Theorems.Thm_GlobalTheory_DimDrop_topologicalKrullDim_lt_of_isClosed
-- name    : GlobalTheory.DimDrop.topologicalKrullDim_lt_of_isClosed
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:49:01.064896+00:00
-- url     : https://prove2.me/theorems/0fc21362-9753-43eb-8865-b64664613ecc
-- title:
--   Dim Drop: topological Krull Dim lt of is Closed
-- statement:
--   The Dim Drop construction uses the topological Krull Dim lt of is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimDropAndFiniteOfDimZero.lean#L39-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimDropAndFiniteOfDimZero.lean#L39-L69

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

theorem GlobalTheory.DimDrop.topologicalKrullDim_lt_of_isClosed (S : Type) [TopologicalSpace S] [NoetherianSpace S]
    (C : Set S) (d : ℕ) (hC : IsClosed C) (hS : topologicalKrullDim S ≤ d)
    (hZ : ∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) :
    topologicalKrullDim C < d := by sorry
