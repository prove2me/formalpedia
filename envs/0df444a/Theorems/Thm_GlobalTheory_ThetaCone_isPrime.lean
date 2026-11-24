-- Prove2me | Theorems.Thm_GlobalTheory_ThetaCone_isPrime
-- name    : GlobalTheory.ThetaCone.isPrime
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:04:39.105093+00:00
-- url     : https://prove2.me/theorems/3adebaaf-3846-4059-880e-5c9809ea7284
-- title:
--   Theta Cone: is Prime
-- statement:
--   The Theta Cone construction uses the is Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ThetaConeIdealIsPrimeAndRingKrullDimLe.lean#L59-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ThetaConeIdealIsPrimeAndRingKrullDimLe.lean#L59-L72

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

theorem GlobalTheory.ThetaCone.isPrime [FiniteDimensional ℂ E] {φ : ι → E → ℂ} (hφ : ∀ c, Differentiable ℂ (φ c))
    {I : Ideal (MvPolynomial ι ℂ)}
    (hI : ∀ F, F ∈ I ↔ ∀ (t : ℂ) (z : E), eval (fun c => t * φ c z) F = 0) : I.IsPrime := by sorry
