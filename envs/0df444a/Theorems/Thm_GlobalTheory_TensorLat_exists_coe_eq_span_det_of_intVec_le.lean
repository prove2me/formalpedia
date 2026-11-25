-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_exists_coe_eq_span_det_of_intVec_le
-- name    : GlobalTheory.TensorLat.exists_coe_eq_span_det_of_intVec_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:04:15.548351+00:00
-- url     : https://prove2.me/theorems/0b17a2ee-2a0c-5466-a477-0d690e1b9aa6
-- title:
--   Tensor Lat: exists coe eq span det of int Vec le
-- statement:
--   The Tensor Lat construction uses the exists coe eq span det of int Vec le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoeEqSpanDetOfIntVecLe.lean#L115-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoeEqSpanDetOfIntVecLe.lean#L115-L144

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsIntSmulMemSpan
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCE
import Definitions.Def_ReciprocityTheory_DualLattices_WedgeNeZeroOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
open scoped nonZeroDivisors
open ReciprocityTheory.MultiplicativeHeights.SemiDegIdx ReciprocityTheory.PGsh
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem GlobalTheory.TensorLat.exists_coe_eq_span_det_of_intVec_le (X : Submodule (𝓞 K) (Fin n → K)) (hfg : X.FG)
    (hstd : intVec K n ≤ X) :
    ∃ J : FractionalIdeal (𝓞 K)⁰ K, (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ X) ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J * ((intVec K n).toAddSubgroup.relIndex X.toAddSubgroup : ℚ) = 1 := by sorry
