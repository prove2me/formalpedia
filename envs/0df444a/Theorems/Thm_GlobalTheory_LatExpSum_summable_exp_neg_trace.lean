-- Prove2me | Theorems.Thm_GlobalTheory_LatExpSum_summable_exp_neg_trace
-- name    : GlobalTheory.LatExpSum.summable_exp_neg_trace
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:22.787238+00:00
-- url     : https://prove2.me/theorems/a6428d4b-01ed-495f-936c-6b29e82b4839
-- title:
--   Lat Exp Sum: summable exp neg trace
-- statement:
--   The Lat Exp Sum construction uses the summable exp neg trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableExpNegTraceTotallyPositiveFractionalIdea.lean#L68-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SummableExpNegTraceTotallyPositiveFractionalIdea.lean#L68-L134

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableExpNegTraceTotallyPositiveFractionalIdea
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
noncomputable section
open GlobalTheory GlobalTheory.LatExpSum

theorem GlobalTheory.LatExpSum.summable_exp_neg_trace : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) (δ : ℝ), 0 < δ → Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by sorry
