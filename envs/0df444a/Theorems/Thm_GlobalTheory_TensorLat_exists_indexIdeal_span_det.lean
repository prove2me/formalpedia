-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_exists_indexIdeal_span_det
-- name    : GlobalTheory.TensorLat.exists_indexIdeal_span_det
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T17:05:00.825489+00:00
-- url     : https://prove2.me/theorems/a325cf80-a138-5b6f-a2c0-48e25e4e837a
-- title:
--   Tensor Lat: exists index Ideal span det
-- statement:
--   The Tensor Lat construction uses the exists index Ideal span det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoeEqSpanDetOfIntVecLe.lean#L236-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsCoeEqSpanDetOfIntVecLe.lean#L236-L258

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

theorem GlobalTheory.TensorLat.exists_indexIdeal_span_det {Λ Λ' : Submodule (𝓞 K) (Fin n → K)} (hle : Λ ≤ Λ')
    (hfg : Λ'.FG) (hsp : Submodule.span K (Λ : Set (Fin n → K)) = ⊤) :
    ∃ 𝔫 : Ideal (𝓞 K), 𝔫 ≠ ⊥ ∧ Ideal.absNorm 𝔫 = Λ.toAddSubgroup.relIndex Λ'.toAddSubgroup ∧
      ∀ 𝔪 : Ideal (𝓞 K), Submodule.span (𝓞 K)
          {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ) ∧ d = (Matrix.of v).det} =
        𝔪 • Submodule.span (𝓞 K)
          {d | ∃ v : Fin n → Fin n → K, (∀ i, v i ∈ Λ') ∧ d = (Matrix.of v).det} ↔ 𝔪 = 𝔫 := by sorry
