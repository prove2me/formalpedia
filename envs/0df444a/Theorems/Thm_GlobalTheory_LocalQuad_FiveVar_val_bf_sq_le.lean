-- Prove2me | Theorems.Thm_GlobalTheory_LocalQuad_FiveVar_val_bf_sq_le
-- name    : GlobalTheory.LocalQuad.FiveVar.val_bf_sq_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:39:41.474719+00:00
-- url     : https://prove2.me/theorems/58b061a9-4723-4a8e-af01-0a62e20f3883
-- title:
--   Five Var: val bf sq le
-- statement:
--   The Five Var construction uses the val bf sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L48-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsZeroFiveOfValuation.lean#L48-L102

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

theorem GlobalTheory.LocalQuad.FiveVar.val_bf_sq_le (h2 : (2 : K) ≠ 0) (v : Valuation K ℤᵐ⁰)
    (hsq : ∀ x : K, v (x - 1) < v 4 → IsSquare x) (a : n → K)
    (han : ∀ x, qf a x = 0 → x = 0) (x y : n → K) :
    v (bf a x y) ^ 2 ≤ v (qf a x) * v (qf a y) := by sorry
