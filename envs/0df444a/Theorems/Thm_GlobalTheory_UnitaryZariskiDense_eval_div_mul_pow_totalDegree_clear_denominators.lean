-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryZariskiDense_eval_div_mul_pow_totalDegree_clear_denominators
-- name    : GlobalTheory.UnitaryZariskiDense.eval_div_mul_pow_totalDegree_clear_denominators
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:47:43.447434+00:00
-- url     : https://prove2.me/theorems/32a2a220-3f24-4615-81ad-7f6c6abfce50
-- title:
--   Unitary Zariski Dense: eval div mul pow total Degree clear denominators
-- statement:
--   The Unitary Zariski Dense construction uses the eval div mul pow total Degree clear denominators property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L175-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/UnitaryGroupFamilyZariskiDense.lean#L175-L191

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

theorem GlobalTheory.UnitaryZariskiDense.eval_div_mul_pow_totalDegree_clear_denominators {σ : Type} (Q : MvPolynomial σ ℂ) (p : σ → ℂ) (D : ℂ) (hD : D ≠ 0) :
    eval (fun v => p v / D) Q * D ^ Q.totalDegree =
      ∑ d ∈ Q.support, coeff d Q * (∏ v ∈ d.support, p v ^ d v) *
        D ^ (Q.totalDegree - d.sum fun _ e => e) := by sorry
