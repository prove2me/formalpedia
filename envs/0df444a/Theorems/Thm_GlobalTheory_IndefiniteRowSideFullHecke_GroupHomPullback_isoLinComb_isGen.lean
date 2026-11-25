-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_GroupHomPullback_isoLinComb_isGen
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.isoLinComb_isGen
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:08:54.222871+00:00
-- url     : https://prove2.me/theorems/34332e0e-8129-4d4b-96f6-7adc04eb8dba
-- title:
--   Group Hom Pullback: iso Lin Comb is Gen
-- statement:
--   The Group Hom Pullback construction uses the iso Lin Comb is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/GroupHomPullback.lean#L120-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/AbelianSchemeLaw/GroupHomPullback.lean#L120-L136

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.GroupHomPullback.isoLinComb_isGen {L M : LB X} {u : LB.Iso L M} (hu : u.IsGen) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : (isoLinComb u φ ε).IsGen := by sorry
