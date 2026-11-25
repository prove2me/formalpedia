-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_Model_rat_finite_place
-- name    : GlobalTheory.QuadSymbol.Model.rat_finite_place
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:20.514998+00:00
-- url     : https://prove2.me/theorems/b372b2b4-81fe-49b0-b454-4b5f24692da1
-- title:
--   Model: rat finite place
-- statement:
--   The Model construction uses the rat finite place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L163-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L163-L170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_NegOneNotSqSqrtTwo
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
open GlobalTheory.QuadSymbol
open GlobalTheory GlobalTheory.QuadSymbol GlobalTheory.QuadSymbol.Model

theorem GlobalTheory.QuadSymbol.Model.rat_finite_place (H : GlobalTheory.Published.QuadraticClassFieldTheory) :
    ∃ v : HeightOneSpectrum (𝓞 ℚ), finDiag ℚ (-1) v ∉
      normGroup ℚ (QuadraticAlgebra ℚ (-1) 0) (v.adicCompletion ℚ) := by sorry
