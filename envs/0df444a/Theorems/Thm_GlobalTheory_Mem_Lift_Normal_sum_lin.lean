-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_Normal_sum_lin
-- name    : GlobalTheory.Mem.Lift.Normal.sum_lin
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:29:33.249582+00:00
-- url     : https://prove2.me/theorems/0a3f9d84-ac4a-4873-9334-c660d0e1ab05
-- title:
--   Normal: sum lin
-- statement:
--   The Normal construction uses the sum lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfNormal.lean#L65-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsQuadOfNormal.lean#L65-L74

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

theorem GlobalTheory.Mem.Lift.Normal.sum_lin (X : Matrix ι ι ℂ) (A : (ι → ℂ) →ₗ[ℂ] ℂ) (v : ι → ℂ) :
    ∑ k, ∑ j, X k j * (v j * A (Pi.single k 1)) = A (X *ᵥ v) := by sorry
