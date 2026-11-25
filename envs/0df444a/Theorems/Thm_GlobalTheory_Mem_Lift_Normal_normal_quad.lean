-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_Normal_normal_quad
-- name    : GlobalTheory.Mem.Lift.Normal.normal_quad
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:14.458228+00:00
-- url     : https://prove2.me/theorems/385afe35-f9e5-5116-8f4c-0a14972cc975
-- title:
--   Normal: normal quad
-- statement:
--   The Normal construction uses the normal quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfNormal.lean#L207-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfNormal.lean#L207-L211

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfNormal
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
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.Normal
variable {ι : Type}
variable [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.Mem.Lift.Normal.normal_quad : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H X : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → Xᴴ * H + H * X = 0 → ∃ (κ : Type) (_ : Fintype κ) (c : κ → ℂ) (p q : κ → ι → ℂ), IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) c p q ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ f, Sm ρ f → quad ρ c p q f = nOp ρ H X f := by sorry
