-- Prove2me | Theorems.Thm_GlobalTheory_QuadSymbol_Model_eta_split
-- name    : GlobalTheory.QuadSymbol.Model.eta_split
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:20:15.236698+00:00
-- url     : https://prove2.me/theorems/7bbf6e72-25ab-4290-8293-885a63a1c501
-- title:
--   Model: eta split
-- statement:
--   The Model construction uses the eta split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/NegOneNotSqSqrtTwo.lean#L37-L43

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
variable {K : Type} [Field K] (d : K) [Fact (∀ r : K, r ^ 2 ≠ d + 0 * r)]

theorem GlobalTheory.QuadSymbol.Model.eta_split {A : Type} [Field A] [Algebra K A] (h2 : (2 : A) ≠ 0) {s : A} (hs0 : s ≠ 0)
    (hs : s ^ 2 = algebraMap K A d) (x : Aˣ) : eta K (QuadraticAlgebra K d 0) A x = 1 := by sorry
