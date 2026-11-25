-- Prove2me | Theorems.Thm_GlobalTheory_LatticeIndicator_forall_mul_map_mem_range_iff
-- name    : GlobalTheory.LatticeIndicator.forall_mul_map_mem_range_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:54.682896+00:00
-- url     : https://prove2.me/theorems/4f38512a-5ea4-5339-b4aa-e067826595fd
-- title:
--   Lattice Indicator: forall mul map mem range iff
-- statement:
--   The Lattice Indicator construction uses the forall mul map mem range iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L299-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsEqSumIndicatorOfRightInvariant.lean#L299-L310

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
open GlobalTheory.LatticeIndicator

theorem GlobalTheory.LatticeIndicator.forall_mul_map_mem_range_iff {O K m n : Type*} [CommRing O] [CommRing K] [Algebra O K]
    [Fintype n] [DecidableEq n] (x : Matrix m n K) (k : GL n O) :
    (∀ i j, (x * (k : Matrix n n O).map (algebraMap O K)) i j ∈ (algebraMap O K).range) ↔
      ∀ i j, x i j ∈ (algebraMap O K).range := by sorry
