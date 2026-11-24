-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finset_basicOpen_cover_inf_of_isAffineOpen
-- name    : GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:37.188231+00:00
-- url     : https://prove2.me/theorems/2102c795-b87f-4383-8163-f9d36fa48ad0
-- title:
--   T: exists finset basic Open cover inf of is Affine Open
-- statement:
--   The T construction uses the exists finset basic Open cover inf of is Affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffineInterFiniteBasicOpenCoverStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffineInterFiniteBasicOpenCoverStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineInterFiniteBasicOpenCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineInterFiniteBasicOpenCoverStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finset_basicOpen_cover_inf_of_isAffineOpen : ∀ (X : Scheme.{0}), IsNoetherian X → ∀ (W V : X.Opens), IsAffineOpen W → IsAffineOpen V → ∃ s : Finset Γ(X, W), (∀ h ∈ s, ∃ r : Γ(X, V), X.basicOpen h = X.basicOpen r) ∧ ((W ⊓ V : X.Opens) : Set X) ⊆ ⋃ h ∈ s, (X.basicOpen h : Set X) := by sorry
