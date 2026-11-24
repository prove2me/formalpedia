-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_clearQ
-- name    : GlobalTheory.UnitaryZariskiDense.eval_clearQ
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:48:04.715068+00:00
-- url     : https://prove2.me/theorems/6267e228-a1f5-4a18-8a5f-95ca24b372d5
-- title:
--   Unitary Zariski Dense: eval clear Q
-- statement:
--   The Unitary Zariski Dense construction uses the eval clear Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L193-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L193-L208

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDense
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.UnitaryZariskiDense
variable {ι : Type} {a : ℕ}
variable [Fintype ι]

theorem GlobalTheory.UnitaryZariskiDense.eval_clearQ (Q : MvPolynomial (ι × Fin a × Fin a) ℂ) (x : ι × Fin a × Fin a → ℂ)
    (hdet : ∀ τ, (1 + famOf x τ).det ≠ 0) :
    eval x (clearQ Q) = eval (fun v => cay (famOf x v.1) v.2.1 v.2.2) Q * (eval x denom) ^ Q.totalDegree := by sorry
