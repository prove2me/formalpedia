-- Prove2me | Theorems.Thm_GlobalTheory_NodalCubic_dblXYZ_param
-- name    : GlobalTheory.NodalCubic.dblXYZ_param
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:51:37.314014+00:00
-- url     : https://prove2.me/theorems/5e5ed28c-034e-4128-9614-da8d0f3ef710
-- title:
--   Nodal Cubic: dbl XYZ param
-- statement:
--   The Nodal Cubic construction uses the dbl XYZ param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonsingularIffNodal.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonsingularIffNodal.lean#L24-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonsingularIffNodal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.NodalCubic
open WeierstrassCurve WeierstrassCurve.Projective

theorem GlobalTheory.NodalCubic.dblXYZ_param {k : Type} [Field k] (u : k) :
    (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.dblXYZ
      ![u * (1 - u), u ^ 2, (1 - u) ^ 3]
      = u ^ 3 • ![(u * u) * (1 - u * u), (u * u) ^ 2, (1 - u * u) ^ 3] := by sorry
