-- Prove2me | Theorems.Thm_GlobalTheory_exists_eq_sum_indicator_of_left_invariant
-- name    : GlobalTheory.exists_eq_sum_indicator_of_left_invariant
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:45.723812+00:00
-- url     : https://prove2.me/theorems/420e5b05-bb28-5f91-b694-a536b3f3a273
-- title:
--   Global Theory: exists eq sum indicator of left invariant
-- statement:
--   The Global Theory construction uses the exists eq sum indicator of left invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L395-L427
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L395-L427

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

theorem GlobalTheory.exists_eq_sum_indicator_of_left_invariant {a b : O} (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : Matrix m n K → R)
    (hinv : ∀ (x : Matrix m n K) (k : GL m O),
      φ ((k : Matrix m m O).map (algebraMap O K) * x) = φ x)
    (hsupp : ∀ x : Matrix m n K, φ x ≠ 0 →
      ∀ i j, (algebraMap O K a • x) i j ∈ (algebraMap O K).range)
    (hper : ∀ x y : Matrix m n K, (∀ i j, y i j ∈ (algebraMap O K).range) →
      φ (x + algebraMap O K b • y) = φ x) :
    ∃ (r : ℕ) (g : Fin r → GL n K) (c : Fin r → R), ∀ x : Matrix m n K,
      φ x = ∑ l, c l * Set.indicator {y : Matrix m n K | ∀ i j, y i j ∈ (algebraMap O K).range}
        1 (x * (g l : Matrix n n K)) := by sorry
