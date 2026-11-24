-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_Ccr_pair_inv
-- name    : GlobalTheory.Mem.Lift.Ccr.pair_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:33:32.043455+00:00
-- url     : https://prove2.me/theorems/bfb2a6bb-b08c-4b89-85c3-86708d213939
-- title:
--   Ccr: pair inv
-- statement:
--   The Ccr construction uses the pair inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIsCCRXOpDOp.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIsCCRXOpDOp.lean#L36-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionUnitaryGroupHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeisenbergSmoothOfWeakDerivativeClosedSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_PolarConjTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_CommuteGelfandInvariantMatrixUnitsOfGlRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsIsCCRXOpDOp
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
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.Ccr

theorem GlobalTheory.Mem.Lift.Ccr.pair_inv {ι : Type} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (k l : ι) :
    star (H⁻¹ *ᵥ Pi.single l 1) ⬝ᵥ H *ᵥ Pi.single k 1 = if k = l then (1 : ℂ) else 0 := by sorry
