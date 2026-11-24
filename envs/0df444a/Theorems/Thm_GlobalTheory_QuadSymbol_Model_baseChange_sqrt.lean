-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_Model_baseChange_sqrt
-- name    : GlobalTheory.QuadSymbol.Model.baseChange_sqrt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:09:25.573611+00:00
-- url     : https://prove2.me/theorems/ecc19600-f09a-4278-addc-34cdc78cfe86
-- title:
--   Model: base Change sqrt
-- statement:
--   The Model construction uses the base Change sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L108-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L108-L129

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
variable {F K : Type} [Field F] [Field K] [Algebra F K] (d : F)

theorem GlobalTheory.QuadSymbol.Model.baseChange_sqrt [NumberField F] [NumberField K] [Fact (∀ r : F, r ^ 2 ≠ d + 0 * r)]
    [Fact (∀ r : K, r ^ 2 ≠ algebraMap F K d + 0 * r)] (H : GlobalTheory.Published.QuadraticClassFieldTheory) :
    (∀ v : HeightOneSpectrum (𝓞 F), BaseChangeAt F (QuadraticAlgebra F d 0) K
      (QuadraticAlgebra K (algebraMap F K d) 0) (v.adicCompletion F)) ∧
    ∀ v : InfinitePlace F, BaseChangeAt F (QuadraticAlgebra F d 0) K
      (QuadraticAlgebra K (algebraMap F K d) 0) v.Completion := by sorry
