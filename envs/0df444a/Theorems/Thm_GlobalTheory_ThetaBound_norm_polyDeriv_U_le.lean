-- Prove2me | Theorems.Thm_GlobalTheory_ThetaBound_norm_polyDeriv_U_le
-- name    : GlobalTheory.ThetaBound.norm_polyDeriv_U_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:42:09.146619+00:00
-- url     : https://prove2.me/theorems/0d7e9a61-0709-4768-bcbc-f7d7ba0a5e72
-- title:
--   Theta Bound: norm poly Deriv U le
-- statement:
--   The Theta Bound construction uses the norm poly Deriv U le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PointwiseNormSqPullbackTensorEqProd.lean#L96-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PointwiseNormSqPullbackTensorEqProd.lean#L96-L119

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_L2NormFundamentalDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_SupLeL2PrincipalTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardToMultisetEqDegree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_PointwiseNormSqPullbackTensorEqProd
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open GlobalTheory.ThetaBound
open TensorLat
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.ThetaBound.norm_polyDeriv_U_le (X : PT E) (q : ℕ) {n : ℕ} (F : (Fin n → Vsp X.dim) → ℂ)
    (hF : Differentiable ℂ F) (S : ℝ) (hS : ∀ v, X.ptN2 q F v ≤ S)
    (P : MvPolynomial (Letter n X.dim) ℂ) (a : ℕ) (hP : P.IsHomogeneous a)
    (b : Fin n → Vsp X.dim) :
    ‖polyDeriv P dir (X.U q b F) 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * Real.sqrt S *
        (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by sorry
