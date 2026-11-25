-- Prove2me | Theorems.Thm_GlobalTheory_NodalCubic_nonsingular_points
-- name    : GlobalTheory.NodalCubic.nonsingular_points
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:51:25.980904+00:00
-- url     : https://prove2.me/theorems/ba90adb4-0578-4808-ac2c-68fbf2ff3bbd
-- title:
--   Nodal Cubic: nonsingular points
-- statement:
--   The Nodal Cubic construction uses the nonsingular points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonsingularIffNodal.lean#L51-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/NonsingularIffNodal.lean#L51-L88

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

theorem GlobalTheory.NodalCubic.nonsingular_points : ∀ (k : Type) [Field k], (∀ u : kˣ, (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.Nonsingular ![(u : k) * (1 - u), (u : k) ^ 2, (1 - (u : k)) ^ 3]) ∧ (∀ u v : kˣ, ∃ c : kˣ, (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.add ![(u : k) * (1 - u), (u : k) ^ 2, (1 - (u : k)) ^ 3] ![(v : k) * (1 - v), (v : k) ^ 2, (1 - (v : k)) ^ 3] = (c : k) • ![((u * v : kˣ) : k) * (1 - (u * v : kˣ)), ((u * v : kˣ) : k) ^ 2, (1 - ((u * v : kˣ) : k)) ^ 3]) ∧ ∀ P : Fin 3 → k, (⟨1, 0, 0, 0, 0⟩ : WeierstrassCurve k).toProjective.Nonsingular P → P 1 ≠ 0 ∧ P 0 + P 1 ≠ 0 ∧ ∃ c : kˣ, P = (c : k) • ![(P 1 / (P 0 + P 1)) * (1 - P 1 / (P 0 + P 1)), (P 1 / (P 0 + P 1)) ^ 2, (1 - P 1 / (P 0 + P 1)) ^ 3] := by sorry
