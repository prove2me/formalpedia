-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Chr_valued_algebraMap_eq_one
-- name    : GlobalTheory.Mem.Chr.valued_algebraMap_eq_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:23:15.110462+00:00
-- url     : https://prove2.me/theorems/03e0e47a-47a7-4e0b-b996-2002910e626a
-- title:
--   Chr: valued algebra Map eq one
-- statement:
--   The Chr construction uses the valued algebra Map eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ValuedAlgebraMapEqOne.lean#L42-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ValuedAlgebraMapEqOne.lean#L42-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ValuedAlgebraMapEqOne
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
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Chr
variable (L : Type) [Field L] [NumberField L]

theorem GlobalTheory.Mem.Chr.valued_algebraMap_eq_one (v : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) (hx : x ∉ v.asIdeal) :
    Valued.v (algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L x)) = 1 := by sorry
