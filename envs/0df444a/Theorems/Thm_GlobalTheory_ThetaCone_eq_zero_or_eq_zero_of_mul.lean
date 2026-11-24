-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCone_eq_zero_or_eq_zero_of_mul
-- name    : GlobalTheory.ThetaCone.eq_zero_or_eq_zero_of_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:04:33.16043+00:00
-- url     : https://prove2.me/theorems/0a87ccd3-edc0-4525-84dd-76ca6f70054b
-- title:
--   Theta Cone: eq zero or eq zero of mul
-- statement:
--   The Theta Cone construction uses the eq zero or eq zero of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ThetaConeIdealIsPrimeAndRingKrullDimLe.lean#L42-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ThetaConeIdealIsPrimeAndRingKrullDimLe.lean#L42-L57

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

theorem GlobalTheory.ThetaCone.eq_zero_or_eq_zero_of_mul [FiniteDimensional ℂ E] {f g : E → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) (h : ∀ z, f z * g z = 0) :
    (∀ z, f z = 0) ∨ ∀ z, g z = 0 := by sorry
