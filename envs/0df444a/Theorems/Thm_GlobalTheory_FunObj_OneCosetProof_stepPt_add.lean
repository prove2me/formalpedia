-- Prove2me | Theorems.Thm_GlobalTheory_FunObj_OneCosetProof_stepPt_add
-- name    : GlobalTheory.FunObj.OneCosetProof.stepPt_add
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:40:23.266248+00:00
-- url     : https://prove2.me/theorems/d984ad2b-03e7-4f1f-ab6d-444d383614ea
-- title:
--   One Coset Proof: step Pt add
-- statement:
--   The One Coset Proof construction uses the step Pt add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OneCosetOfIsTensor.lean#L14-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsKOOfDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCosetOfIsTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.OneCosetProof
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type} [Field k]

theorem GlobalTheory.FunObj.OneCosetProof.stepPt_add {n n' : Type} {c : ℕ} (x₀ : Matrix n n' k) (e : StepVar n c n' → k)
    (Y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (hY : ∀ r s, ¬ Free (c / 2 + 1) (r, s) → Y r s = 0) :
    stepPt x₀ (e + fun rs => Y rs.1.1 rs.1.2) = stepPt x₀ e + Y := by sorry
