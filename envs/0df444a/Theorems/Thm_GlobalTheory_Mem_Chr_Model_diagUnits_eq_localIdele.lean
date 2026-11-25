-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Chr_Model_diagUnits_eq_localIdele
-- name    : GlobalTheory.Mem.Chr.Model.diagUnits_eq_localIdele
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:16.677184+00:00
-- url     : https://prove2.me/theorems/e8868a77-9300-4a95-a1db-2e1ee856d587
-- title:
--   Model: diag Units eq local Idele
-- statement:
--   The Model construction uses the diag Units eq local Idele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L94-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L94-L102

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

theorem GlobalTheory.Mem.Chr.Model.diagUnits_eq_localIdele (v : HeightOneSpectrum (𝓞 L)) (a : Lˣ) (x : (v.adicCompletion L)ˣ)
    (h : diagUnits L a = localIdele L v x) : a = 1 := by sorry
