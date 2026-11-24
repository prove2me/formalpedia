-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eq_zero_of_eval_real
-- name    : GlobalTheory.UnitaryZariskiDense.eq_zero_of_eval_real
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:46:18.493805+00:00
-- url     : https://prove2.me/theorems/ec5d1773-585d-469f-880e-4178acd6d59a
-- title:
--   Unitary Zariski Dense: eq zero of eval real
-- statement:
--   The Unitary Zariski Dense construction uses the eq zero of eval real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L14-L22

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

theorem GlobalTheory.UnitaryZariskiDense.eq_zero_of_eval_real {σ : Type} (P : MvPolynomial σ ℂ)
    (h : ∀ u : σ → ℝ, eval (fun v => (u v : ℂ)) P = 0) : P = 0 := by sorry
