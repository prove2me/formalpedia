-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCone_eval_mul_of_isHomogeneous
-- name    : GlobalTheory.ThetaCone.eval_mul_of_isHomogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:25.373026+00:00
-- url     : https://prove2.me/theorems/d456ec8a-69d9-4baf-b27b-c93376562994
-- title:
--   Theta Cone: eval mul of is Homogeneous
-- statement:
--   The Theta Cone construction uses the eval mul of is Homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ThetaConeIdealIsPrimeAndRingKrullDimLe.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ThetaConeIdealIsPrimeAndRingKrullDimLe.lean#L20-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ThetaConeIdealIsPrimeAndRingKrullDimLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ThetaCone
open MvPolynomial Filter Topology Module ReciprocityTheory.ChartRestriction.G.AR.Up.IntPf
attribute [local instance] MvPolynomial.gradedAlgebra
variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.ThetaCone.eval_mul_of_isHomogeneous (q : ι → ℂ) (t : ℂ) {G : MvPolynomial ι ℂ} {m : ℕ}
    (hG : G.IsHomogeneous m) : eval (fun i => t * q i) G = t ^ m * eval q G := by sorry
