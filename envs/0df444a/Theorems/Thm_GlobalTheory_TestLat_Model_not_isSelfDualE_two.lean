-- Prove2me | Theorems.Thm_GlobalTheory_TestLat_Model_not_isSelfDualE_two
-- name    : GlobalTheory.TestLat.Model.not_isSelfDualE_two
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:42:54.922446+00:00
-- url     : https://prove2.me/theorems/5af3f4d6-f5ed-5e25-a240-9a2c7d6896b4
-- title:
--   Model: not is Self Dual E two
-- statement:
--   The Model construction uses the not is Self Dual E two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L154-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L154-L180

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

theorem GlobalTheory.TestLat.Model.not_isSelfDualE_two (σ : K →+* K) :
    ¬ IsSelfDualE σ (1 : Matrix (Fin 1) (Fin 1) K) (Submodule.span (𝓞 K) {fun _ => (2 : K)}) := by sorry
