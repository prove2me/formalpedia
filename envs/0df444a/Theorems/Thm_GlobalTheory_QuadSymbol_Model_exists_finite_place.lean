-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_Model_exists_finite_place
-- name    : GlobalTheory.QuadSymbol.Model.exists_finite_place
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:09:40.06758+00:00
-- url     : https://prove2.me/theorems/45ec8561-6661-44f5-bf3a-ea1cb2ef16f3
-- title:
--   Model: exists finite place
-- statement:
--   The Model construction uses the exists finite place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L82-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L82-L97

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
variable {K : Type} [Field K] [Fact (∀ r : K, r ^ 2 ≠ -1 + 0 * r)]

theorem GlobalTheory.QuadSymbol.Model.exists_finite_place [NumberField K] (w : InfinitePlace K) (hw : w.IsReal)
    (hu : ∀ w', w' = w) (H : GlobalTheory.Published.QuadraticClassFieldTheory) :
    ∃ v : HeightOneSpectrum (𝓞 K),
      eta K (QuadraticAlgebra K (-1) 0) (v.adicCompletion K) (finDiag K (-1) v) = -1 := by sorry
