-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_denom
-- name    : GlobalTheory.UnitaryZariskiDense.eval_denom
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:22.27913+00:00
-- url     : https://prove2.me/theorems/203d9614-e19d-4eeb-a29b-91104e0964dc
-- title:
--   Unitary Zariski Dense: eval denom
-- statement:
--   The Unitary Zariski Dense construction uses the eval denom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L166-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L166-L168

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

theorem GlobalTheory.UnitaryZariskiDense.eval_denom (x : ι × Fin a × Fin a → ℂ) :
    eval x (denom (ι := ι) (a := a)) = ∏ τ, (1 + famOf x τ).det := by sorry
