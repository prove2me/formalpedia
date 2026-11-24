-- Prove2me | Theorems.Thm_GlobalTheory_exists_eq_sum_indicator_of_right_invariant
-- name    : GlobalTheory.exists_eq_sum_indicator_of_right_invariant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:37.345423+00:00
-- url     : https://prove2.me/theorems/7eae4a01-d805-4e71-8671-640e72a94797
-- title:
--   Global Theory: exists eq sum indicator of right invariant
-- statement:
--   The Global Theory construction uses the exists eq sum indicator of right invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L322-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L322-L393

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsEqSumIndicatorOfRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
open LatticeIndicator
variable {O K m n R : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [CommRing R]

theorem GlobalTheory.exists_eq_sum_indicator_of_right_invariant {a b : O} (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : Matrix m n K → R)
    (hinv : ∀ (x : Matrix m n K) (k : GL n O),
      φ (x * (k : Matrix n n O).map (algebraMap O K)) = φ x)
    (hsupp : ∀ x : Matrix m n K, φ x ≠ 0 →
      ∀ i j, (algebraMap O K a • x) i j ∈ (algebraMap O K).range)
    (hper : ∀ x y : Matrix m n K, (∀ i j, y i j ∈ (algebraMap O K).range) →
      φ (x + algebraMap O K b • y) = φ x) :
    ∃ (r : ℕ) (h : Fin r → GL m K) (c : Fin r → R), ∀ x : Matrix m n K,
      φ x = ∑ l, c l * Set.indicator {y : Matrix m n K | ∀ i j, y i j ∈ (algebraMap O K).range}
        1 ((((h l)⁻¹ : GL m K) : Matrix m m K) * x) := by sorry
