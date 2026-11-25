-- Prove2me | Theorems.Thm_GlobalTheory_TestLat_Model_isSelfDualK_std
-- name    : GlobalTheory.TestLat.Model.isSelfDualK_std
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:34.066436+00:00
-- url     : https://prove2.me/theorems/91d9de8f-5087-4850-bdfa-04cffd550034
-- title:
--   Model: is Self Dual K std
-- statement:
--   The Model construction uses the is Self Dual K std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L146-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L146-L152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.TestLat GlobalTheory.TestLat.Model
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}

theorem GlobalTheory.TestLat.Model.isSelfDualK_std [StarRing K] : IsSelfDualK (1 : Matrix (Fin n) (Fin n) K) (stdLat K n) := by sorry
