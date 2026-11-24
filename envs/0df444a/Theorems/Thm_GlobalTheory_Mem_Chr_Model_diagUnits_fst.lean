-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Chr_Model_diagUnits_fst
-- name    : GlobalTheory.Mem.Chr.Model.diagUnits_fst
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:23:09.21718+00:00
-- url     : https://prove2.me/theorems/ea63d1bf-dc5c-41b9-9164-08f9b2693aad
-- title:
--   Model: diag Units fst
-- statement:
--   The Model construction uses the diag Units fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L69-L70

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

theorem GlobalTheory.Mem.Chr.Model.diagUnits_fst (w : InfinitePlace L) (a : Lˣ) :
    ((diagUnits L a : Ideles L) : AdeleRing (𝓞 L) L).1 w = algebraMap L w.Completion a := by sorry
