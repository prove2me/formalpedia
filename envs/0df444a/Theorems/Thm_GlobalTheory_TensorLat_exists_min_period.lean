-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_exists_min_period
-- name    : GlobalTheory.TensorLat.exists_min_period
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T17:53:00.512856+00:00
-- url     : https://prove2.me/theorems/5d697503-6650-51c8-b29c-f52e1feb3735
-- title:
--   Tensor Lat: exists min period
-- statement:
--   The Tensor Lat construction uses the exists min period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormalisedThetaValueBound.lean#L71-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormalisedThetaValueBound.lean#L71-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LeMulNormFlatOfSelfDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormalisedThetaValueBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem GlobalTheory.TensorLat.exists_min_period (T : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ T.L, x ≠ 0 → lam ≤ ‖x‖) :
    ∃ lam' : ℝ, 0 < lam' ∧ (∀ γ ∈ tensorLat T Λ', γ ≠ 0 → lam' ≤ ‖flat γ‖) ∧
      (1 + 4 * Real.sqrt (2 * Fintype.card (Fin n × Idx T.dim)) / (Real.sqrt Real.pi * lam')) ^
          Fintype.card (Fin n × Idx T.dim) =
        (1 + 4 * Real.sqrt (2 * Fintype.card (Idx T.dim) * n) *
          (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^
          (Fintype.card (Idx T.dim) * n) := by sorry
