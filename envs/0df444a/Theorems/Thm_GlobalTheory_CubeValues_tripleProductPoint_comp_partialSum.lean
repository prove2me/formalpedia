-- Prove2me | Theorems.Thm_GlobalTheory_CubeValues_tripleProductPoint_comp_partialSum
-- name    : GlobalTheory.CubeValues.tripleProductPoint_comp_partialSum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:31:38.562864+00:00
-- url     : https://prove2.me/theorems/85b8b0c4-d234-47e7-950e-b295692a8ed9
-- title:
--   Cube Values: triple Product Point comp partial Sum
-- statement:
--   The Cube Values construction uses the triple Product Point comp partial Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L141-L145

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.CubeValues
variable {A : Over (Sp ℂ)} [GrpObj A] {L₀ : LB A.left} {g : ℕ} (u : HolUnif A L₀ g)

theorem GlobalTheory.CubeValues.tripleProductPoint_comp_partialSum (x : Fin 3 → Fin g → ℂ) (I : Finset (Fin 3)) :
    (pt3 u x).left ≫ (psum A (x3 A) I).left = (u.ex (∑ a ∈ I, x a)).left := by sorry
