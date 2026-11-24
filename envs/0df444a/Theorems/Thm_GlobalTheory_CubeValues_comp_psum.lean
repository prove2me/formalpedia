-- Prove2me | Theorems.Thm_GlobalTheory_CubeValues_comp_psum
-- name    : GlobalTheory.CubeValues.comp_psum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:22:20.077844+00:00
-- url     : https://prove2.me/theorems/b13611be-d4ff-412e-ad87-b03634470b98
-- title:
--   Cube Values: comp psum
-- statement:
--   The Cube Values construction uses the comp psum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L127-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/CubeTrivialisationOnUniformisingSpace.lean#L127-L136

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

theorem GlobalTheory.CubeValues.comp_psum {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A))
    (w : Fin n → Fin g → ℂ) (h : ∀ k, p ≫ y k = u.ex (w k)) (I : Finset (Fin n)) :
    p ≫ psum A y I = u.ex (∑ a ∈ I, w a) := by sorry
