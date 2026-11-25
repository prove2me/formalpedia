-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Chr_Model_localIdele_continuous
-- name    : GlobalTheory.Mem.Chr.Model.localIdele_continuous
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:18.745488+00:00
-- url     : https://prove2.me/theorems/b43f1af5-0104-4365-899e-74446043cc2d
-- title:
--   Model: local Idele continuous
-- statement:
--   The Model construction uses the local Idele continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L91-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/DiagUnitsEqLocalIdele.lean#L91-L92

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

theorem GlobalTheory.Mem.Chr.Model.localIdele_continuous (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by sorry
