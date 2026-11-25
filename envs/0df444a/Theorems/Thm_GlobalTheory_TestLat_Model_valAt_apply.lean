-- Prove2me | Theorems.Thm_GlobalTheory_TestLat_Model_valAt_apply
-- name    : GlobalTheory.TestLat.Model.valAt_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:23.01046+00:00
-- url     : https://prove2.me/theorems/9b5ef241-f8ae-52ad-aacb-c3fafa4d8299
-- title:
--   Model: val At apply
-- statement:
--   The Model construction uses the val At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L25-L27

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
omit [NumberField K]

theorem GlobalTheory.TestLat.Model.valAt_apply (lam : ι → DomWeight n) (e : Fin N ≃ C × VVIdx lam) (c : C) (u : Fin N → K) :
    valAt lam e c u = ∑ i, u (e.symm (c, i)) • bVV K lam i := by sorry
