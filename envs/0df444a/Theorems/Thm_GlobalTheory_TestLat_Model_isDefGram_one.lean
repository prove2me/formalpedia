-- Prove2me | Theorems.Thm_GlobalTheory_TestLat_Model_isDefGram_one
-- name    : GlobalTheory.TestLat.Model.isDefGram_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:55:27.248302+00:00
-- url     : https://prove2.me/theorems/70d02687-eb03-53fe-961e-75f49d79e1c1
-- title:
--   Model: is Def Gram one
-- statement:
--   The Model construction uses the is Def Gram one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L100-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotIsSelfDualETwo.lean#L100-L109

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

theorem GlobalTheory.TestLat.Model.isDefGram_one [StarRing K] : IsDefGram (1 : Matrix (Fin n) (Fin n) K) := by sorry
