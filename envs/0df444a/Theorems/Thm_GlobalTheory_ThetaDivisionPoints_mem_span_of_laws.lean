-- Prove2me | Theorems.Thm_GlobalTheory_ThetaDivisionPoints_mem_span_of_laws
-- name    : GlobalTheory.ThetaDivisionPoints.mem_span_of_laws
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:13:52.290506+00:00
-- url     : https://prove2.me/theorems/3d99cb31-0ab1-5517-8c9a-d0c5efc59fa5
-- title:
--   Theta Division Points: mem span of laws
-- statement:
--   The Theta Division Points construction uses the mem span of laws property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsThetaDivisionPointNeZero.lean#L63-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsThetaDivisionPointNeZero.lean#L63-L85

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

theorem GlobalTheory.ThetaDivisionPoints.mem_span_of_laws {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ SiegelH (Fin g)) {N : ℕ}
    (hN : 1 ≤ N) {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f ∧
      (∀ (i : Fin g) z, f (z + Pi.single i 1) = f z) ∧
      ∀ (j : Fin g) z, f (z + τ.mulVec (Pi.single j 1)) =
        eC (-(τ j j) / 2) ^ N * cexp (-(2 * Real.pi * I) * N * z j) * f z) :
    f ∈ Submodule.span ℂ (Set.range (fun (c : Fin g → Fin N) (z : Fin g → ℂ) =>
      theta (fun i => ((c i : ℕ) : ℝ) / N) 0 ((N : ℂ) • z) ((N : ℂ) • τ))) := by sorry
