-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GroupHomPullback_res_prod_pr
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.res_prod_pr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:13:59.82065+00:00
-- url     : https://prove2.me/theorems/32ccb0d7-15a6-4f0d-b46a-d2890fe65f6a
-- title:
--   Group Hom Pullback: res prod pr
-- statement:
--   The Group Hom Pullback construction uses the res prod pr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/GroupHomPullback.lean#L98-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/GroupHomPullback.lean#L98-L101

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_GroupHomPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
universe u
variable {X X' Y Y' : Scheme.{u}}
variable {K : Type u} [Fintype K]

theorem GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.res_prod_pr (φ : K → (Y ⟶ X)) (ε : K → ℤ) {U : K → X.Opens} {V W : Y.Opens}
    (h : ∀ k, V ≤ φ k ⁻¹ᵁ U k) (h' : W ≤ V) (a : ∀ k, Γ(X, U k)ˣ) :
    res h' (∏ k, pr (φ k) (h k) (a k) ^ ε k) = ∏ k, pr (φ k) (h'.trans (h k)) (a k) ^ ε k := by sorry
