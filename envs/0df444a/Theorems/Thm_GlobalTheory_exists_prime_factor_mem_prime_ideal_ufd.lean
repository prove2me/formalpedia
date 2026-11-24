-- Prove2me | Theorems.Thm_GlobalTheory_exists_prime_factor_mem_prime_ideal_ufd
-- name    : GlobalTheory.exists_prime_factor_mem_prime_ideal_ufd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:36:32.294015+00:00
-- url     : https://prove2.me/theorems/28cccec7-1ce2-4f6f-bb44-e926fbdb018f
-- title:
--   Global Theory: exists prime factor mem prime ideal ufd
-- statement:
--   The Global Theory construction uses the exists prime factor mem prime ideal ufd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HypersurfaceDiffIsPreirreducibleOfNoSplitting.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HypersurfaceDiffIsPreirreducibleOfNoSplitting.lean#L8-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HypersurfaceDiffIsPreirreducibleOfNoSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
open GlobalTheory

theorem GlobalTheory.exists_prime_factor_mem_prime_ideal_ufd {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (I : Ideal R) [hI : I.IsPrime] (a : R) (ha : a ≠ 0)
    (haI : a ∈ I) : ∃ u : R, Prime u ∧ u ∣ a ∧ u ∈ I := by sorry
