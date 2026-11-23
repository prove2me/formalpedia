-- Prove2me | Theorems.Thm_GlobalTheory_T_evenOrderNorms_one_add_four_mul_of_no_root
-- name    : GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:48:21.598699+00:00
-- url     : https://prove2.me/theorems/2250bf4d-3a34-4cbf-b180-1331a6ad9144
-- title:
--   T: even Order Norms one add four mul of no root
-- statement:
--   The T construction uses the even Order Norms one add four mul of no root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EvenOrderNormsOneAddFourMulOfNoRootStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/EvenOrderNormsOneAddFourMulOfNoRootStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenOrderNormsOneAddFourMulOfNoRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EvenOrderNormsOneAddFourMulOfNoRootStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (ρ : K), (2 : K) ≠ 0 → w ρ ≤ 1 → (∀ x : K, w x ≤ 1 → w (x ^ 2 + x - ρ) = 1) → EvenNorms w (1 + 4 * ρ) := by sorry
