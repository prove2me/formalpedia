-- Prove2me | Theorems.Thm_GlobalTheory_SelfCube_herm_conj
-- name    : GlobalTheory.SelfCube.herm_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:52.052849+00:00
-- url     : https://prove2.me/theorems/294cfd23-e073-4737-aab7-7704c281ecc6
-- title:
--   Self Cube: herm conj
-- statement:
--   The Self Cube construction uses the herm conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AppellHumbertDataOfIsoCube.lean#L188-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/AppellHumbertDataOfIsoCube.lean#L188-L193

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
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
open GlobalTheory GlobalTheory.SelfCube
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

theorem GlobalTheory.SelfCube.herm_conj (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = starRingEnd ℂ (hermForm Hm z w) := by sorry
