-- Prove2me | Theorems.Thm_GlobalTheory_DegPull_nonempty_cubical_pull
-- name    : GlobalTheory.DegPull.nonempty_cubical_pull
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:02.350039+00:00
-- url     : https://prove2.me/theorems/bc6626c8-4716-4764-bf50-3a09c35429d8
-- title:
--   Deg Pull: nonempty cubical pull
-- statement:
--   The Deg Pull construction uses the nonempty cubical pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonemptyCubicalPull.lean#L147-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonemptyCubicalPull.lean#L147-L162

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
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
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.DegPull
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
variable {S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}

theorem GlobalTheory.DegPull.nonempty_cubical_pull (gp : IsGrpPullback G' G f F) {L : RigLB G} (c : CubicalStr G L) (L' : RigLB G')
    {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w) : Nonempty (CubicalStr G' L') := by sorry
