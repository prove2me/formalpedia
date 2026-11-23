-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_exists_unit_mul_sq_sub_one_lt
-- name    : GlobalTheory.QNorm.exists_unit_mul_sq_sub_one_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:09.8658+00:00
-- url     : https://prove2.me/theorems/93055c93-3f5a-4a6b-b748-9ac7ce376584
-- title:
--   QNorm: exists unit mul sq sub one lt
-- statement:
--   The QNorm construction uses the exists unit mul sq sub one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitMulSqQuadraticDefectStep.lean#L9-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsUnitMulSqQuadraticDefectStep.lean#L9-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitMulSqQuadraticDefectStep
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
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.exists_unit_mul_sq_sub_one_lt :
    ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (δ π : K) (k : ℕ), w π = WithZero.exp (-1) → (∀ x : K, w x ≤ 1 → ∃ y : K, w y ≤ 1 ∧ w (x - y ^ 2) < 1) → w δ = 1 → w 4 < w (δ - 1) → w (δ - 1) = WithZero.exp (-(2 * (k : ℤ))) → ∃ c : K, w c = 1 ∧ w (δ * c ^ 2 - 1) < w (δ - 1) := by sorry
