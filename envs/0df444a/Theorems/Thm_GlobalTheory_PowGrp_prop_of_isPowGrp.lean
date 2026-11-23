-- Prove2me | Theorems.Thm_GlobalTheory_PowGrp_prop_of_isPowGrp
-- name    : GlobalTheory.PowGrp.prop_of_isPowGrp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:44:14.260556+00:00
-- url     : https://prove2.me/theorems/2f20ab5a-eba6-4be4-93f2-f462c233629c
-- title:
--   Pow Grp: prop of is Pow Grp
-- statement:
--   The Pow Grp construction uses the prop of is Pow Grp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SmoothIsMultiplicative.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SmoothIsMultiplicative.lean#L33-L37

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SmoothIsMultiplicative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowGrp
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
attribute [local instance] smooth_isMultiplicative

theorem GlobalTheory.PowGrp.prop_of_isPowGrp (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) (hG : P G.hom) : P G'.hom := by sorry
