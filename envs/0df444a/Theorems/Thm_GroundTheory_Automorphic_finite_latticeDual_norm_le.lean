-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_finite_latticeDual_norm_le
-- name    : GroundTheory.Automorphic.finite_latticeDual_norm_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:20.647868+00:00
-- url     : https://prove2.me/theorems/f1ff6724-3933-44a5-a392-a13c22cfac3e
-- title:
--   Automorphic: finite lattice Dual norm le
-- statement:
--   The Automorphic construction uses the finite lattice Dual norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Reduction.lean#L37-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/Reduction.lean#L37-L69

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Submodule
open scoped RealInnerProductSpace
universe u
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

theorem GroundTheory.Automorphic.finite_latticeDual_norm_le [FiniteDimensional ℝ X] {L : AddSubgroup X}
    (hL : span ℝ (L : Set X) = ⊤) (C : ℝ) :
    ({y | y ∈ latticeDual L ∧ ‖y‖ ≤ C} : Set X).Finite := by sorry
