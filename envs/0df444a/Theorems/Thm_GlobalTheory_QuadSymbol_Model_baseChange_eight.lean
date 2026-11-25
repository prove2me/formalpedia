-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_Model_baseChange_eight
-- name    : GlobalTheory.QuadSymbol.Model.baseChange_eight
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:19:55.499858+00:00
-- url     : https://prove2.me/theorems/1945590e-d933-5f64-b867-99e7f3b92aea
-- title:
--   Model: base Change eight
-- statement:
--   The Model construction uses the base Change eight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L149-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L149-L161

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

theorem GlobalTheory.QuadSymbol.Model.baseChange_eight (H : GlobalTheory.Published.QuadraticClassFieldTheory) :
    ∃ _ : Fact (∀ r : QuadraticAlgebra ℚ 2 0,
        r ^ 2 ≠ algebraMap ℚ (QuadraticAlgebra ℚ 2 0) (-1) + 0 * r),
      ∀ v : HeightOneSpectrum (𝓞 ℚ), BaseChangeAt ℚ (QuadraticAlgebra ℚ (-1) 0) (QuadraticAlgebra ℚ 2 0)
        (QuadraticAlgebra (QuadraticAlgebra ℚ 2 0) (algebraMap ℚ (QuadraticAlgebra ℚ 2 0) (-1)) 0)
        (v.adicCompletion ℚ) := by sorry
