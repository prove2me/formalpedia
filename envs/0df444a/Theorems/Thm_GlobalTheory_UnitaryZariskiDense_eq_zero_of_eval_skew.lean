-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eq_zero_of_eval_skew
-- name    : GlobalTheory.UnitaryZariskiDense.eq_zero_of_eval_skew
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:46:13.973824+00:00
-- url     : https://prove2.me/theorems/64ae5fc2-7f35-4ab8-8561-26c1b8044df4
-- title:
--   Unitary Zariski Dense: eq zero of eval skew
-- statement:
--   The Unitary Zariski Dense construction uses the eq zero of eval skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L50-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L50-L76

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

theorem GlobalTheory.UnitaryZariskiDense.eq_zero_of_eval_skew (R : MvPolynomial (ι × Fin a × Fin a) ℂ)
    (h : ∀ x : ι × Fin a × Fin a → ℂ, (∀ v, star (x (tr v)) = - x v) → eval x R = 0) : R = 0 := by sorry
