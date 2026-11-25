-- Prove2me | Theorems.Thm_GlobalTheory_CubeLawCompare_locally_trivial_of_iso_pull
-- name    : GlobalTheory.CubeLawCompare.locally_trivial_of_iso_pull
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:40.479864+00:00
-- url     : https://prove2.me/theorems/ea1fc184-2158-503a-a6dc-794015ba852a
-- title:
--   Cube Law Compare: locally trivial of iso pull
-- statement:
--   The Cube Law Compare construction uses the locally trivial of iso pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocallyTrivialOfIsoPull.lean#L86-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocallyTrivialOfIsoPull.lean#L86-L102

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_RigidityTranslation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocallyTrivialOfIsoPull
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CubeLawCompare
variable {Y T : Scheme.{0}}

theorem GlobalTheory.CubeLawCompare.locally_trivial_of_iso_pull (p : Y ⟶ T) (M : LB Y) {N : LB T} (hN : N.IsLB)
    (u : LB.Iso (N.pull p) M) (hu : u.IsGen) (t : T) :
    ∃ V : T.Opens, t ∈ V ∧ ∃ c : LB.Gen (M.pull (p ⁻¹ᵁ V).ι), c.IsGen := by sorry
