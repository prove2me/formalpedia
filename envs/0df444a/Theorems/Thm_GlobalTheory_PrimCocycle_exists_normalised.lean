-- Prove2me | Theorems.Thm_GlobalTheory_PrimCocycle_exists_normalised
-- name    : GlobalTheory.PrimCocycle.exists_normalised
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:56:36.238898+00:00
-- url     : https://prove2.me/theorems/3793816b-0c23-4f47-ab42-85dc6b29c466
-- title:
--   Prim Cocycle: exists normalised
-- statement:
--   The Prim Cocycle construction uses the exists normalised property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/PrimitiveCocycle.lean#L47-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/PrimitiveCocycle.lean#L47-L62

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_PrimitiveCocycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PrimCocycle
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

theorem GlobalTheory.PrimCocycle.exists_normalised {L : LB B.left} (hL : L.IsLB) (t : LB.Gen (LB.LinComb L (lamφ B) lamε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (lamφ B) lamε), u.IsGen ∧
      ∀ (T : Over S) (z : T.left) (J), Good L z J → val₂ u z J (1 : T ⟶ B) 1 = 1 := by sorry
