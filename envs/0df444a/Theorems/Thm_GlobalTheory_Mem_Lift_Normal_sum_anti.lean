-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_Normal_sum_anti
-- name    : GlobalTheory.Mem.Lift.Normal.sum_anti
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:29:46.333644+00:00
-- url     : https://prove2.me/theorems/75dae9f0-2aff-44d3-a7c8-3178e6a12474
-- title:
--   Normal: sum anti
-- statement:
--   The Normal construction uses the sum anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfNormal.lean#L76-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfNormal.lean#L76-L120

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

theorem GlobalTheory.Mem.Lift.Normal.sum_anti {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (hX : Xᴴ * H + H * X = 0)
    (A : (ι → ℂ) →ₗ⋆[ℂ] ℂ) (v : ι → ℂ) :
    ∑ k, ∑ j, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * A (H⁻¹ *ᵥ Pi.single j 1)) = - A (X *ᵥ v) := by sorry
