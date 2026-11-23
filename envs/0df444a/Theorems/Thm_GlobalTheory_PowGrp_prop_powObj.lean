-- Prove2me | Theorems.Thm_GlobalTheory_PowGrp_prop_powObj
-- name    : GlobalTheory.PowGrp.prop_powObj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:21.684309+00:00
-- url     : https://prove2.me/theorems/a3300b19-d03f-4af2-9402-da21d1d6aeff
-- title:
--   Pow Grp: prop pow Obj
-- statement:
--   The Pow Grp construction uses the prop pow Obj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SmoothIsMultiplicative.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SmoothIsMultiplicative.lean#L15-L20

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

theorem GlobalTheory.PowGrp.prop_powObj (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    (G : Over S) (hG : P G.hom) : ∀ n : ℕ, P (powObj G n).hom
  := by sorry
