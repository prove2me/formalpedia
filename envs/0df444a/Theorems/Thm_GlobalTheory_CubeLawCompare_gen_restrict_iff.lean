-- Prove2me | Theorems.Thm_GlobalTheory_CubeLawCompare_gen_restrict_iff
-- name    : GlobalTheory.CubeLawCompare.gen_restrict_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:50.810139+00:00
-- url     : https://prove2.me/theorems/4ce61b1e-09f5-4596-97e4-c09b91f9c230
-- title:
--   Cube Law Compare: gen restrict iff
-- statement:
--   The Cube Law Compare construction uses the gen restrict iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocallyTrivialOfIsoPull.lean#L28-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LocallyTrivialOfIsoPull.lean#L28-L84

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

theorem GlobalTheory.CubeLawCompare.gen_restrict_iff (M : LB Y) (W : Y.Opens) :
    (∃ c : LB.Gen (M.pull W.ι), c.IsGen) ↔ ∃ d, IsGenOn M W d := by sorry
