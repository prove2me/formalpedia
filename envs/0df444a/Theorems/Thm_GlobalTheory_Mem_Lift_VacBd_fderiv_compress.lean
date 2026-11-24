-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_VacBd_fderiv_compress
-- name    : GlobalTheory.Mem.Lift.VacBd.fderiv_compress
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:22:53.629423+00:00
-- url     : https://prove2.me/theorems/3bb8f909-35e6-45df-a9ca-3aecc7deb628
-- title:
--   Vac Bd: fderiv compress
-- statement:
--   The Vac Bd construction uses the fderiv compress property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FderivCompress.lean#L109-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FderivCompress.lean#L109-L115

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FderivCompress
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.VacBd
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
  {ρ : V → B →L[ℂ] B}
set_option linter.unusedSectionVars false

theorem GlobalTheory.Mem.Lift.VacBd.fderiv_compress (P : B →L[ℂ] B) {g y : B} (hg : Sm ρ g) {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (e : ∀ w, P (ρ w g) = φ w • y) (w v : V) : P (fderiv ℝ (fun u => ρ u g) w v) = fderiv ℝ φ w v • y := by sorry
