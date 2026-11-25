-- Prove2me | Theorems.Thm_GlobalTheory_ThetaBound_norm_polyDeriv_pullback_tensor_le
-- name    : GlobalTheory.ThetaBound.norm_polyDeriv_pullback_tensor_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:43:40.056449+00:00
-- url     : https://prove2.me/theorems/b91b9e9c-d821-4b95-ab02-94748932b3a6
-- title:
--   Theta Bound: norm poly Deriv pullback tensor le
-- statement:
--   The Theta Bound construction uses the norm poly Deriv pullback tensor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PointwiseNormSqPullbackTensorEqProd.lean#L173-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PointwiseNormSqPullbackTensorEqProd.lean#L173-L198

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

theorem GlobalTheory.ThetaBound.norm_polyDeriv_pullback_tensor_le (X : PT E) {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim}
    (hπ : ∀ v w, Hf (π v) (π w) = q * Hf v w) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ X.L, x ≠ 0 → lam ≤ ‖x‖)
    (P : MvPolynomial (Letter n X.dim) ℂ) (a : ℕ) (hP : P.IsHomogeneous a)
    (b : Fin n → Vsp X.dim) :
    ‖polyDeriv P dir (X.U q b (s0 X π s)) 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx X.dim)) /
          (Real.sqrt Real.pi * lam)) ^ Fintype.card (Idx X.dim)) ^ n *
        Real.sqrt (X.l2 1 s) ^ n := by sorry
