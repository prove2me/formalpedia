-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Chr_Model_infIdele_injective
-- name    : GlobalTheory.Mem.Chr.Model.infIdele_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:02.734302+00:00
-- url     : https://prove2.me/theorems/e8037210-77eb-54c4-b380-67f22d5cc63a
-- title:
--   Model: inf Idele injective
-- statement:
--   The Model construction uses the inf Idele injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L47-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_DiagUnitsEqLocalIdele
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Chr.Model
variable (L : Type) [Field L] [NumberField L]

theorem GlobalTheory.Mem.Chr.Model.infIdele_injective (w : InfinitePlace L) : Function.Injective (infIdele L w) := by sorry
