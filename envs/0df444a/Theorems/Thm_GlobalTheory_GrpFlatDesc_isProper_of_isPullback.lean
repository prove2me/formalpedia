-- Prove2me | Theorems.Thm_GlobalTheory_GrpFlatDesc_isProper_of_isPullback
-- name    : GlobalTheory.GrpFlatDesc.isProper_of_isPullback
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:31.999804+00:00
-- url     : https://prove2.me/theorems/94b657ba-f139-4fbc-b768-bc88cc7880d1
-- title:
--   Grp Flat Desc: is Proper of is Pullback
-- statement:
--   The Grp Flat Desc construction uses the is Proper of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GroupSchemeMorphismDescends.lean#L30-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/GroupSchemeMorphismDescends.lean#L30-L47

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GrpObjOfDenseOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupSchemeMorphismDescends
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GrpFlatDesc
open GrpDense MorphismProperty
variable {Z U : Scheme.{0}}
set_option backward.isDefEq.respectTransparency.types false

theorem GlobalTheory.GrpFlatDesc.isProper_of_isPullback {A G : Scheme.{0}} {φ : A ⟶ G} {f : A ⟶ U} {g : G ⟶ Z} {j : U ⟶ Z}
    [Flat j] [Surjective j] [QuasiCompact j] (h : IsPullback φ f g j) [IsProper f] : IsProper g := by sorry
