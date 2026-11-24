-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_Ccr_exists_om
-- name    : GlobalTheory.Mem.Lift.Ccr.exists_om
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:34:23.833996+00:00
-- url     : https://prove2.me/theorems/f62eb2a0-da2c-49c3-8b7b-ef2a73bd81f1
-- title:
--   Ccr: exists om
-- statement:
--   The Ccr construction uses the exists om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIsCCRXOpDOp.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsIsCCRXOpDOp.lean#L21-L28

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

theorem GlobalTheory.Mem.Lift.Ccr.exists_om {ι : Type} [Fintype ι] (H : Matrix ι ι ℂ) :
    ∃ om : (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ, ∀ x y, om x y = (star y ⬝ᵥ H *ᵥ x).im := by sorry
