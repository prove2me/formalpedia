-- Prove2me | Theorems.Thm_GlobalTheory_SW_SiegelSum_summable_pi_prod
-- name    : GlobalTheory.SW.SiegelSum.summable_pi_prod
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:44:47.446299+00:00
-- url     : https://prove2.me/theorems/0340522a-7621-4087-83f8-e8cba17ddfb3
-- title:
--   Siegel Sum: summable pi prod
-- statement:
--   The Siegel Sum construction uses the summable pi prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableNormSiegelThetaSeriesTerms.lean#L10-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SummableNormSiegelThetaSeriesTerms.lean#L10-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableProdPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.SiegelSum

theorem GlobalTheory.SW.SiegelSum.summable_pi_prod {J A : Type} [Fintype J] (f : J → A → ℝ) (h0 : ∀ j a, 0 ≤ f j a)
    (hs : ∀ j, Summable (f j)) : Summable fun n : J → A => ∏ j, f j (n j) := by sorry
