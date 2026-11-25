-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GroupHomPullback_res_res
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.res_res
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:57.812715+00:00
-- url     : https://prove2.me/theorems/1d5b3b79-dc5e-49d7-a054-998cdfa176a1
-- title:
--   Group Hom Pullback: res res
-- statement:
--   The Group Hom Pullback construction uses the res res property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/GroupHomPullback.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/GroupHomPullback.lean#L26-L30

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.res_res {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by sorry
