-- Prove2me | Theorems.Thm_GlobalTheory_mem_span_indicator_of_right_invariant
-- name    : GlobalTheory.mem_span_indicator_of_right_invariant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:15.349588+00:00
-- url     : https://prove2.me/theorems/a251f259-4f94-483d-ad5c-a30b87edd5d5
-- title:
--   Global Theory: mem span indicator of right invariant
-- statement:
--   The Global Theory construction uses the mem span indicator of right invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L429-L448
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L429-L448

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

theorem GlobalTheory.mem_span_indicator_of_right_invariant {a b : O} (ha : a ≠ 0) (hb : b ≠ 0)
    (φ : Matrix m n K → R)
    (hinv : ∀ (x : Matrix m n K) (k : GL n O),
      φ (x * (k : Matrix n n O).map (algebraMap O K)) = φ x)
    (hsupp : ∀ x : Matrix m n K, φ x ≠ 0 →
      ∀ i j, (algebraMap O K a • x) i j ∈ (algebraMap O K).range)
    (hper : ∀ x y : Matrix m n K, (∀ i j, y i j ∈ (algebraMap O K).range) →
      φ (x + algebraMap O K b • y) = φ x) :
    φ ∈ Submodule.span R (Set.range fun (h : GL m K) (x : Matrix m n K) =>
      Set.indicator {y : Matrix m n K | ∀ i j, y i j ∈ (algebraMap O K).range}
        (1 : Matrix m n K → R) (((h⁻¹ : GL m K) : Matrix m m K) * x)) := by sorry
