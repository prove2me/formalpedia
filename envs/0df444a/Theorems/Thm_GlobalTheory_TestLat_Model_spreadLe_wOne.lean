-- Prove2me | Theorems.Thm_GlobalTheory_TestLat_Model_spreadLe_wOne
-- name    : GlobalTheory.TestLat.Model.spreadLe_wOne
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:28.802683+00:00
-- url     : https://prove2.me/theorems/5dfd56a8-333c-5800-a260-a3c5cf823b09
-- title:
--   Model: spread Le w One
-- statement:
--   The Model construction uses the spread Le w One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L184-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L184-L189

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

theorem GlobalTheory.TestLat.Model.spreadLe_wOne (R : ℝ) : SpreadLe (fun _ : Unit => wOne) R ↔ 1 ≤ R := by sorry
