-- Prove2me | Theorems.Thm_GlobalTheory_linForm_eq_dotProduct
-- name    : GlobalTheory.linForm_eq_dotProduct
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:58.628529+00:00
-- url     : https://prove2.me/theorems/a19f91c2-fdc2-4a94-824e-a00aa5ff2c82
-- title:
--   Global Theory: lin Form eq dot Product
-- statement:
--   The Global Theory construction uses the lin Form eq dot Product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemPeriodLatticeOfExpThetaLinForm.lean#L47-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/MemPeriodLatticeOfExpThetaLinForm.lean#L47-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfExpThetaLinForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.linForm_eq_dotProduct {g : ℕ} (lam : (Fin g → ℂ) →ₗ[ℂ] ℂ) (z : Fin g → ℂ) :
    lam z = (fun i => lam (Pi.single i 1)) ⬝ᵥ z := by sorry
