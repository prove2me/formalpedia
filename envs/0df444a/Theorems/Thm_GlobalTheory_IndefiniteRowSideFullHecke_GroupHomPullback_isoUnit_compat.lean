-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GroupHomPullback_isoUnit_compat
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.isoUnit_compat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:14:09.992386+00:00
-- url     : https://prove2.me/theorems/45a139d6-7314-4183-b0fb-df4c930d76b3
-- title:
--   Group Hom Pullback: iso Unit compat
-- statement:
--   The Group Hom Pullback construction uses the iso Unit compat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/GroupHomPullback.lean#L103-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/GroupHomPullback.lean#L103-L114

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.isoUnit_compat {L M : LB X} {u : LB.Iso L M} (hu : u.IsGen) (j j' : M.ι) (i i' : L.ι)
    (f : Y ⟶ X) {W : Y.Opens} (h : W ≤ f ⁻¹ᵁ (M.U j ⊓ L.U i)) (h' : W ≤ f ⁻¹ᵁ (M.U j' ⊓ L.U i'))
    (hM : W ≤ f ⁻¹ᵁ (M.U j ⊓ M.U j')) (hL : W ≤ f ⁻¹ᵁ (L.U i ⊓ L.U i')) :
    pr f h (isoUnit u j i) =
      pr f hM (M.g j j') * (pr f hL (L.g i i'))⁻¹ * pr f h' (isoUnit u j' i') := by sorry
