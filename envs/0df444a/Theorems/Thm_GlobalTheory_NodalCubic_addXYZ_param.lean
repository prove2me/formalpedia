-- Prove2me | Theorems.Thm_GlobalTheory_NodalCubic_addXYZ_param
-- name    : GlobalTheory.NodalCubic.addXYZ_param
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:52:04.039056+00:00
-- url     : https://prove2.me/theorems/a19f8c58-a2ff-4eff-9024-5c5a2a87febe
-- title:
--   Nodal Cubic: add XYZ param
-- statement:
--   The Nodal Cubic construction uses the add XYZ param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonsingularIffNodal.lean#L15-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonsingularIffNodal.lean#L15-L21

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

theorem GlobalTheory.NodalCubic.addXYZ_param {k : Type} [Field k] (u v : k) :
    (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.addXYZ
      ![u * (1 - u), u ^ 2, (1 - u) ^ 3] ![v * (1 - v), v ^ 2, (1 - v) ^ 3]
      = (u - v) ^ 3 • ![(u * v) * (1 - u * v), (u * v) ^ 2, (1 - u * v) ^ 3] := by sorry
