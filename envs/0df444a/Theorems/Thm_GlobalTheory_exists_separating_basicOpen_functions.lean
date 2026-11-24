-- Prove2me | Theorems.Thm_GlobalTheory_exists_separating_basicOpen_functions
-- name    : GlobalTheory.exists_separating_basicOpen_functions
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:08.273822+00:00
-- url     : https://prove2.me/theorems/b664e19d-be01-4fb0-8910-26999c776bec
-- title:
--   Global Theory: exists separating basic Open functions
-- statement:
--   The Global Theory construction uses the exists separating basic Open functions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSeparatingBasicOpenFunctions.lean#L6-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSeparatingBasicOpenFunctions.lean#L6-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSeparatingBasicOpenFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory

theorem GlobalTheory.exists_separating_basicOpen_functions : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by sorry
