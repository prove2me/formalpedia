-- Prove2me | Theorems.Thm_GlobalTheory_isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces
-- name    : GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:58:32.607072+00:00
-- url     : https://prove2.me/theorems/903d3a6f-93b2-413e-a731-4f5056853828
-- title:
--   Global Theory: is Open of stable Under Generalization of locally Closed pieces
-- statement:
--   The Global Theory construction uses the is Open of stable Under Generalization of locally Closed pieces property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenOfStableUnderGeneralizationOfLocallyClosed.lean#L9-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenOfStableUnderGeneralizationOfLocallyClosed.lean#L9-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfConstructible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyClosed
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
open GlobalTheory

theorem GlobalTheory.isOpen_of_stableUnderGeneralization_of_locallyClosed_pieces :
    ∀ (X : Scheme.{0}) (Z : Set X), StableUnderGeneralization Z → (∀ x ∈ Z, ∃ (W W' : X.Opens) (J : Finset Γ(X, W')), W ≤ W' ∧ x ∈ W ∧ (∀ c ∈ J, x ∉ X.basicOpen c) ∧ ∀ y ∈ W, (∀ c ∈ J, y ∉ X.basicOpen c) → y ∈ Z) → IsOpen Z := by sorry
