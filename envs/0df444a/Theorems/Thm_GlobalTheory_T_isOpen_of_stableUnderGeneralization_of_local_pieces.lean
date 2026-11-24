-- Prove2me | Theorems.Thm_GlobalTheory_T_isOpen_of_stableUnderGeneralization_of_local_pieces
-- name    : GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_local_pieces
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:49:25.725864+00:00
-- url     : https://prove2.me/theorems/0da739e4-424e-409e-9461-27f814daa085
-- title:
--   T: is Open of stable Under Generalization of local pieces
-- statement:
--   The T construction uses the is Open of stable Under Generalization of local pieces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenOfStableUnderGeneralizationOfLocallyClosedStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenOfStableUnderGeneralizationOfLocallyClosedStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyClosedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_local_pieces : ∀ (X : Scheme.{0}) (Z : Set X), StableUnderGeneralization Z → (∀ x ∈ Z, ∃ (W W' : X.Opens) (J : Finset Γ(X, W')), W ≤ W' ∧ x ∈ W ∧ (∀ c ∈ J, x ∉ X.basicOpen c) ∧ ∀ y ∈ W, (∀ c ∈ J, y ∉ X.basicOpen c) → y ∈ Z) → IsOpen Z := by sorry
