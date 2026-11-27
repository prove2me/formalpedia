-- Prove2me | Theorems.Thm_GlobalTheory_T_topologicalKrullDim_drop_and_finite_of_dim_zero
-- name    : GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:05.124495+00:00
-- url     : https://prove2.me/theorems/65e1fd8a-6781-4161-9091-cb0882466bf6
-- title:
--   T: topological Krull Dim drop and finite of dim zero
-- statement:
--   The T construction uses the topological Krull Dim drop and finite of dim zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimDropAndFiniteOfDimZeroStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TopologicalKrullDimDropAndFiniteOfDimZeroStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimDropAndFiniteOfDimZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TopologicalKrullDimDropAndFiniteOfDimZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TopologicalSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.topologicalKrullDim_drop_and_finite_of_dim_zero : ∀ (S : Type) [TopologicalSpace S] [NoetherianSpace S], (∀ (C : Set S) (d : ℕ), IsClosed C → topologicalKrullDim S ≤ d → (∀ Z ∈ irreducibleComponents S, (d : WithBot ℕ∞) ≤ topologicalKrullDim Z → ¬ Z ⊆ C) → topologicalKrullDim C < d) ∧ (T0Space S → topologicalKrullDim S ≤ 0 → Finite S) := by sorry
