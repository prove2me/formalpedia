-- Prove2me | Theorems.Thm_GlobalTheory_T_prod_unitary_mem_unitaryGroup_pi
-- name    : GlobalTheory.T.prod_unitary_mem_unitaryGroup_pi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:28.089752+00:00
-- url     : https://prove2.me/theorems/ca52ee19-ea55-5bd3-a95c-b264cb205e38
-- title:
--   T: prod unitary mem unitary Group pi
-- statement:
--   The T construction uses the prod unitary mem unitary Group pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryTensorPlacesSlotsStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryTensorPlacesSlotsStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryTensorPlacesSlots
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryTensorPlacesSlotsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.prod_unitary_mem_unitaryGroup_pi : ∀ (J ι : Type) [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι] (n : J → ℕ) (C : J → Matrix ι ι ℂ), (∀ j, C j ∈ Matrix.unitaryGroup ι ℂ) → (Matrix.of fun T T' : (∀ j, Fin (n j) → ι) => ∏ j, ∏ r, C j (T j r) (T' j r)) ∈ Matrix.unitaryGroup (∀ j, Fin (n j) → ι) ℂ := by sorry
