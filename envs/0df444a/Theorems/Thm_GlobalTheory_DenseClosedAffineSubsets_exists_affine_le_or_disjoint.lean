-- Prove2me | Theorems.Thm_GlobalTheory_DenseClosedAffineSubsets_exists_affine_le_or_disjoint
-- name    : GlobalTheory.DenseClosedAffineSubsets.exists_affine_le_or_disjoint
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:43:47.722881+00:00
-- url     : https://prove2.me/theorems/64dbbbaf-6dd5-429e-84e4-8f4d8d06f229
-- title:
--   Dense Closed Affine Subsets: exists affine le or disjoint
-- statement:
--   The Dense Closed Affine Subsets construction uses the exists affine le or disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L85-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineLeOrDisjoint.lean#L85-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineLeOrDisjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.DenseClosedAffineSubsets

theorem GlobalTheory.DenseClosedAffineSubsets.exists_affine_le_or_disjoint {W : Scheme.{0}} [Nonempty W] (t : Finset W.Opens) :
    ∃ U : W.Opens, IsAffineOpen U ∧ (U : Set W).Nonempty ∧
      ∀ O ∈ t, U ≤ O ∨ Disjoint (U : Set W) O := by sorry
