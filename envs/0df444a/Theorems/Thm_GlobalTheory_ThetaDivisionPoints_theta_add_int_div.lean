-- Prove2me | Theorems.Thm_GlobalTheory_ThetaDivisionPoints_theta_add_int_div
-- name    : GlobalTheory.ThetaDivisionPoints.theta_add_int_div
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:13:46.959322+00:00
-- url     : https://prove2.me/theorems/d3897fb0-34b0-59e5-b3f8-087d8b7592bd
-- title:
--   Theta Division Points: theta add int div
-- statement:
--   The Theta Division Points construction uses the theta add int div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsThetaDivisionPointNeZero.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsThetaDivisionPointNeZero.lean#L16-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FourierCoeffUnitCubeTranslateOfEntirePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_EntirePeriodicEqZeroOfFourierCoeffEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CardLePowOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ClassicalThetaLevelAndLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemSpanThetaOfLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_RiemannThetaLevelOneNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsApplySubSmulNeZeroAndApplyAddNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsThetaDivisionPointNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix
open GlobalTheory GlobalTheory.ThetaDivisionPoints

theorem GlobalTheory.ThetaDivisionPoints.theta_add_int_div {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ.IsSymm) {N : ℕ}
    (hN : (N : ℂ) ≠ 0) (a : Fin g → ℝ) (z : Fin g → ℂ) (m : Fin g → ℤ) :
    theta a 0 ((N : ℂ) • (z + (N : ℂ)⁻¹ • ofIntVec m)) ((N : ℂ) • τ) =
      eC (ofRealVec a ⬝ᵥ ofIntVec m) * theta a 0 ((N : ℂ) • z) ((N : ℂ) • τ) := by sorry
