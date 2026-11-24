-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_stepPt_joinVars
-- name    : GlobalTheory.FunObj.stepPt_joinVars
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:44:06.047981+00:00
-- url     : https://prove2.me/theorems/826d5560-1f74-44ab-bcba-237f13a13097
-- title:
--   Fun Obj: step Pt join Vars
-- statement:
--   The Fun Obj construction uses the step Pt join Vars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L117-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MeasurePreservingPiProdSplit.lean#L117-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} {c : ℕ} {n' : Type*}

theorem GlobalTheory.FunObj.stepPt_joinVars (x₀ : Matrix n n' k) (w : KeptVar n c n' → k) (f : FreeVar n c n' → k) :
    stepPt x₀ (joinVars (w, f)) = affPt (c / 2 + 1) x₀ f + keptPt w := by sorry
