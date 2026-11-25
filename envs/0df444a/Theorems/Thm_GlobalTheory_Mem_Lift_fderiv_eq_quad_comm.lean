-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_fderiv_eq_quad_comm
-- name    : GlobalTheory.Mem.Lift.fderiv_eq_quad_comm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:23.028533+00:00
-- url     : https://prove2.me/theorems/391485da-52fa-4e3d-ac34-0c10c80dea88
-- title:
--   Lift: fderiv eq quad comm
-- statement:
--   The Lift construction uses the fderiv eq quad comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FderivEqQuadComm.lean#L25-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/FderivEqQuadComm.lean#L25-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FderivEqQuadComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift

theorem GlobalTheory.Mem.Lift.fderiv_eq_quad_comm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ (X : V → V) (κ : Type) [Fintype κ] (c : κ → ℂ) (p q : κ → V), IsQuadOf (fun x y => om x y) X c p q → ∀ f, Sm ρ f → ∀ w, fderiv ℝ (fun u => ρ u f) w (X w) = quad ρ c p q (ρ w f) - ρ w (quad ρ c p q f) := by sorry
