-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_val_det_le
-- name    : GlobalTheory.LocalQuad.FiveVar.val_det_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:13:38.3218+00:00
-- url     : https://prove2.me/theorems/ac5e1f1d-64d3-46b3-a96a-5dac148d8504
-- title:
--   Five Var: val det le
-- statement:
--   The Five Var construction uses the val det le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L106-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L106-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsZeroFiveOfValuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad
open GlobalTheory.LocalQuad.FiveVar
variable {K : Type*} [Field K] {n : Type*} [Fintype n]
variable [DecidableEq n]

theorem GlobalTheory.LocalQuad.FiveVar.val_det_le (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) (P : Matrix n n K) :
    v (∏ i, 2 * a i) * v P.det ^ 2 ≤ ∏ i, v (qf a (P i)) := by sorry
