-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPoint_exists_half_of_sq_eq_one
-- name    : GlobalTheory.ThetaPoint.exists_half_of_sq_eq_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T17:07:18.551185+00:00
-- url     : https://prove2.me/theorems/c2de9d1d-ebb2-5224-a054-769a5a278b5b
-- title:
--   Theta Point: exists half of sq eq one
-- statement:
--   The Theta Point construction uses the exists half of sq eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHalfOfSqEqOne.lean#L89-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsHalfOfSqEqOne.lean#L89-L95

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemPeriodLatticeOfThetaTranslateEqUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHalfOfSqEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.ThetaPoint
open CanTh
variable {g : ℕ}

theorem GlobalTheory.ThetaPoint.exists_half_of_sq_eq_one {c : ℂ} (hc : c ^ 2 = 1) :
    ∃ a : ℝ, (a = 0 ∨ a = 1 / 2) ∧ cexp (2 * π * I * a) = c ∧ cexp (-(2 * π * I * a)) = c := by sorry
