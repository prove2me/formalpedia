-- Prove2me | Theorems.Thm_GlobalTheory_invariant_testFun_eq_sum_indicator
-- name    : GlobalTheory.invariant_testFun_eq_sum_indicator
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:02.878627+00:00
-- url     : https://prove2.me/theorems/2b19f3b1-17d0-4409-b9bc-3b47e2356c78
-- title:
--   Global Theory: invariant test Fun eq sum indicator
-- statement:
--   The Global Theory construction uses the invariant test Fun eq sum indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L452-L467
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L452-L467

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

theorem GlobalTheory.invariant_testFun_eq_sum_indicator {O K : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K]
    [IsFractionRing O K] {ϖ : O} (hϖ : Irreducible ϖ) {M n : ℕ} (N : ℕ)
    (φ : Matrix (Fin M) (Fin n) K → ℂ)
    (hinv : ∀ (x : Matrix (Fin M) (Fin n) K) (k : GL (Fin n) O),
      φ (x * (k : Matrix (Fin n) (Fin n) O).map (algebraMap O K)) = φ x)
    (hsupp : ∀ x : Matrix (Fin M) (Fin n) K, φ x ≠ 0 →
      ∀ i j, (algebraMap O K ϖ ^ N • x) i j ∈ (algebraMap O K).range)
    (hper : ∀ x y : Matrix (Fin M) (Fin n) K, (∀ i j, y i j ∈ (algebraMap O K).range) →
      φ (x + algebraMap O K ϖ ^ N • y) = φ x) :
    ∃ (r : ℕ) (h : Fin r → GL (Fin M) K) (c : Fin r → ℂ), ∀ x : Matrix (Fin M) (Fin n) K,
      φ x = ∑ l, c l * Set.indicator
        {y : Matrix (Fin M) (Fin n) K | ∀ i j, y i j ∈ (algebraMap O K).range}
        1 ((((h l)⁻¹ : GL (Fin M) K) : Matrix (Fin M) (Fin M) K) * x) := by sorry
