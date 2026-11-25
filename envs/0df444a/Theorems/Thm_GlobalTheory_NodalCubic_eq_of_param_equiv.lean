-- Prove2me | Theorems.Thm_GlobalTheory_NodalCubic_eq_of_param_equiv
-- name    : GlobalTheory.NodalCubic.eq_of_param_equiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:51:44.86709+00:00
-- url     : https://prove2.me/theorems/b147751b-d810-489f-8ed0-03aac47cbea3
-- title:
--   Nodal Cubic: eq of param equiv
-- statement:
--   The Nodal Cubic construction uses the eq of param equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonsingularIffNodal.lean#L32-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonsingularIffNodal.lean#L32-L41

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

theorem GlobalTheory.NodalCubic.eq_of_param_equiv {k : Type} [Field k] {u v : k} (hu : u ≠ 0) (hv : v ≠ 0)
    (h : ∃ c : kˣ, c • ![v * (1 - v), v ^ 2, (1 - v) ^ 3] = ![u * (1 - u), u ^ 2, (1 - u) ^ 3]) :
    u = v := by sorry
