-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_numer
-- name    : GlobalTheory.UnitaryZariskiDense.eval_numer
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:47:50.38235+00:00
-- url     : https://prove2.me/theorems/988a9e8e-54e7-4e17-8daf-79ab106949e0
-- title:
--   Unitary Zariski Dense: eval numer
-- statement:
--   The Unitary Zariski Dense construction uses the eval numer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L170-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L170-L173

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

theorem GlobalTheory.UnitaryZariskiDense.eval_numer (x : ι × Fin a × Fin a → ℂ) (v : ι × Fin a × Fin a) :
    eval x (numer v) = ((1 - famOf x v.1) * (1 + famOf x v.1).adjugate) v.2.1 v.2.2 *
      ∏ τ ∈ Finset.univ.erase v.1, (1 + famOf x τ).det := by sorry
