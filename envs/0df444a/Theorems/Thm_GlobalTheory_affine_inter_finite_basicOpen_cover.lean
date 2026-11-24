-- Prove2me | Theorems.Thm_GlobalTheory_affine_inter_finite_basicOpen_cover
-- name    : GlobalTheory.affine_inter_finite_basicOpen_cover
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:05:34.705828+00:00
-- url     : https://prove2.me/theorems/df2d76bd-2ad8-4f60-a15c-f8843a7daa72
-- title:
--   Global Theory: affine inter finite basic Open cover
-- statement:
--   The Global Theory construction uses the affine inter finite basic Open cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffineInterFiniteBasicOpenCover.lean#L7-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffineInterFiniteBasicOpenCover.lean#L7-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineInterFiniteBasicOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry TopologicalSpace
open GlobalTheory

theorem GlobalTheory.affine_inter_finite_basicOpen_cover :
    ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (W V : X.Opens), IsAffineOpen W → IsAffineOpen V →
      ∃ s : Finset Γ(X, W), (∀ h ∈ s, ∃ r : Γ(X, V), X.basicOpen h = X.basicOpen r) ∧
        ((W ⊓ V : X.Opens) : Set X) ⊆ ⋃ h ∈ s, (X.basicOpen h : Set X) := by sorry
