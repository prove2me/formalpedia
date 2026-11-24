-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Chr_Model_finSingle_continuous
-- name    : GlobalTheory.Mem.Chr.Model.finSingle_continuous
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:22:57.117858+00:00
-- url     : https://prove2.me/theorems/90714bb7-71dd-44ac-98e3-5b4bc59a029b
-- title:
--   Model: fin Single continuous
-- statement:
--   The Model construction uses the fin Single continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L72-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L72-L89

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

theorem GlobalTheory.Mem.Chr.Model.finSingle_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (finSingle L v) := by sorry
