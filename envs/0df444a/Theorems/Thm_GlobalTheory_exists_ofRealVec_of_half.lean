-- Prove2me | Theorems.Thm_GlobalTheory_exists_ofRealVec_of_half
-- name    : GlobalTheory.exists_ofRealVec_of_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:14.827791+00:00
-- url     : https://prove2.me/theorems/e5c75aca-e28a-47b2-8f4b-3eae59eed7e4
-- title:
--   Global Theory: exists of Real Vec of half
-- statement:
--   The Global Theory construction uses the exists of Real Vec of half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/PolarisedTorusAlgebraicOfParts.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/PolarisedTorusAlgebraicOfParts.lean#L23-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_PolarisedTorusAlgebraicOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.exists_ofRealVec_of_half {g : ℕ} (a : Fin g → ℂ) (ha : ∀ i, a i = 0 ∨ a i = 1 / 2) :
    ∃ a' : Fin g → ℝ, (∀ i, a' i = 0 ∨ a' i = 1 / 2) ∧ a = ofRealVec a' := by sorry
