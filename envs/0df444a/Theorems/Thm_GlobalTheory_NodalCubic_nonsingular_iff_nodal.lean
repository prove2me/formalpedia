-- Prove2me | Theorems.Thm_GlobalTheory_NodalCubic_nonsingular_iff_nodal
-- name    : GlobalTheory.NodalCubic.nonsingular_iff_nodal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:52:09.035908+00:00
-- url     : https://prove2.me/theorems/f632bc34-0f28-45f9-a50d-59da6a222ab1
-- title:
--   Nodal Cubic: nonsingular iff nodal
-- statement:
--   The Nodal Cubic construction uses the nonsingular iff nodal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonsingularIffNodal.lean#L44-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonsingularIffNodal.lean#L44-L49

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

theorem GlobalTheory.NodalCubic.nonsingular_iff_nodal {k : Type} [Field k] (P : Fin 3 → k) :
    (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.Nonsingular P ↔
      P 1 ^ 2 * P 2 + P 0 * P 1 * P 2 = P 0 ^ 3 ∧
        (P 1 * P 2 ≠ 3 * P 0 ^ 2 ∨ 2 * P 1 * P 2 + P 0 * P 2 ≠ 0 ∨ P 1 ^ 2 + P 0 * P 1 ≠ 0) := by sorry
