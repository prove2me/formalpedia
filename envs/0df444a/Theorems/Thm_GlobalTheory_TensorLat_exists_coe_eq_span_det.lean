-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_exists_coe_eq_span_det
-- name    : GlobalTheory.TensorLat.exists_coe_eq_span_det
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:09:02.947205+00:00
-- url     : https://prove2.me/theorems/0b231d07-7315-47f7-87dc-9e94c2fb4ce6
-- title:
--   Tensor Lat: exists coe eq span det
-- statement:
--   The Tensor Lat construction uses the exists coe eq span det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoeEqSpanDetOfIntVecLe.lean#L146-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoeEqSpanDetOfIntVecLe.lean#L146-L222

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

theorem GlobalTheory.TensorLat.exists_coe_eq_span_det {Λ Λ' : Submodule (𝓞 K) (Fin n → K)} (hle : Λ ≤ Λ') (hfg : Λ'.FG)
    (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ J J' : FractionalIdeal (𝓞 K)⁰ K, J ≠ 0 ∧ J' ≠ 0 ∧
      (J : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ) ∧ d = (Matrix.of v).det} ∧
      (J' : Submodule (𝓞 K) K) = Submodule.span (𝓞 K)
        {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ') ∧ d = (Matrix.of v).det} ∧
      FractionalIdeal.absNorm J =
        (Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup : ℚ) * FractionalIdeal.absNorm J' := by sorry
