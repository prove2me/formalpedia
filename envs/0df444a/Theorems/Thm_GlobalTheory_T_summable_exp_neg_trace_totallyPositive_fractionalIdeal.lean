-- Prove2me | Theorems.Thm_GlobalTheory_T_summable_exp_neg_trace_totallyPositive_fractionalIdeal
-- name    : GlobalTheory.T.summable_exp_neg_trace_totallyPositive_fractionalIdeal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:58:31.992619+00:00
-- url     : https://prove2.me/theorems/4d92bdbe-222d-4af5-8b60-2f830bc1ff42
-- title:
--   T: summable exp neg trace totally Positive fractional Ideal
-- statement:
--   The T construction uses the summable exp neg trace totally Positive fractional Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableExpNegTraceTotallyPositiveFractionalIdeaStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableExpNegTraceTotallyPositiveFractionalIdeaStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableExpNegTraceTotallyPositiveFractionalIdea
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableExpNegTraceTotallyPositiveFractionalIdeaStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.summable_exp_neg_trace_totallyPositive_fractionalIdeal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) (δ : ℝ), 0 < δ → Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by sorry
