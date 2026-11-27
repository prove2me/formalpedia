-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_gram_mul_self_le
-- name    : GroundTheory.Automorphic.gram_mul_self_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:29.988933+00:00
-- url     : https://prove2.me/theorems/81ae5ee8-b85f-41a4-b414-7e796970bff5
-- title:
--   Automorphic: gram mul self le
-- statement:
--   The Automorphic construction uses the gram mul self le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/GramReduction.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/GramReduction.lean#L48-L54

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Reduction
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_GramReduction
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
open Module Matrix Submodule
open scoped RealInnerProductSpace
variable {J : Type*} [Fintype J]

theorem GroundTheory.Automorphic.gram_mul_self_le (G : Matrix J J ℝ) (hs : Gᵀ = G)
    (hpos : ∀ x : J → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x)) (x y : J → ℝ) :
    (x ⬝ᵥ (G *ᵥ y)) * (x ⬝ᵥ (G *ᵥ y)) ≤ (x ⬝ᵥ (G *ᵥ x)) * (y ⬝ᵥ (G *ᵥ y)) := by sorry
