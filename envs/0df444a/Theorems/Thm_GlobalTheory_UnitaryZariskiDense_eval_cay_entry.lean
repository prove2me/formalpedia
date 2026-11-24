-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_cay_entry
-- name    : GlobalTheory.UnitaryZariskiDense.eval_cay_entry
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:47:33.675368+00:00
-- url     : https://prove2.me/theorems/c8e9b98a-79e3-446a-a93d-309353ed87e0
-- title:
--   Unitary Zariski Dense: eval cay entry
-- statement:
--   The Unitary Zariski Dense construction uses the eval cay entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L145-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L145-L151

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

theorem GlobalTheory.UnitaryZariskiDense.eval_cay_entry (x : ι × Fin a × Fin a → ℂ) (τ : ι) (i j : Fin a) :
    eval x (((1 - varMat (a := a) τ) * (1 + varMat τ).adjugate :
      Matrix (Fin a) (Fin a) (MvPolynomial (ι × Fin a × Fin a) ℂ)) i j) =
      ((1 - famOf x τ) * (1 + famOf x τ).adjugate) i j := by sorry
