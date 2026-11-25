-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Chr_Model_diagUnits_snd
-- name    : GlobalTheory.Mem.Chr.Model.diagUnits_snd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:12.907107+00:00
-- url     : https://prove2.me/theorems/19b3c43d-42d3-4369-8605-0af8f922c783
-- title:
--   Model: diag Units snd
-- statement:
--   The Model construction uses the diag Units snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L59-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L59-L60

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

theorem GlobalTheory.Mem.Chr.Model.diagUnits_snd (v : HeightOneSpectrum (𝓞 L)) (a : Lˣ) :
    ((diagUnits L a : Ideles L) : AdeleRing (𝓞 L) L).2 v = algebraMap L (v.adicCompletion L) a := by sorry
