-- Prove2me | Theorems.Thm_GlobalTheory_norm_prod_sign_mul_det_submatrix_sub_one_le
-- name    : GlobalTheory.norm_prod_sign_mul_det_submatrix_sub_one_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:13:51.490396+00:00
-- url     : https://prove2.me/theorems/dc505b64-b2b4-4157-9601-7e1d7cddf716
-- title:
--   Global Theory: norm prod sign mul det submatrix sub one le
-- statement:
--   The Global Theory construction uses the norm prod sign mul det submatrix sub one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L75-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormProdSignMulDetSubmatrixSubOneLe.lean#L75-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory

theorem GlobalTheory.norm_prod_sign_mul_det_submatrix_sub_one_le {r : ℕ} (j : Fin r → ℂ)
    (hj : ∀ a, j a = 1 ∨ j a = -1) (G : Matrix (Fin r) (Fin r) ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hG : ∀ a b, ‖(G - diagonal j) a b‖ ≤ ε) (hr : (r : ℝ) ^ 2 * ε ≤ 1)
    {i : ℕ} {e : Fin i → Fin r} (he : Function.Injective e) :
    ‖(∏ a, j (e a)) * (G.submatrix e e).det - 1‖ ≤ 2 * ((r : ℝ) ^ 2 * ε) := by sorry
