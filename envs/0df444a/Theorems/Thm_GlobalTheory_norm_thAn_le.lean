-- Prove2me | Theorems.Thm_GlobalTheory_norm_thAn_le
-- name    : GlobalTheory.norm_thAn_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T15:42:18.812701+00:00
-- url     : https://prove2.me/theorems/7a57d79d-25fa-4519-8ee3-0305ec3ff3e2
-- title:
--   Global Theory: norm th An le
-- statement:
--   The Global Theory construction uses the norm th An le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PointwiseNormSqPullbackTensorEqProd.lean#L232-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/PointwiseNormSqPullbackTensorEqProd.lean#L232-L246

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

theorem GlobalTheory.norm_thAn_le {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    {X : ReciprocityTheory.ChartRestriction.G.FD.Data E r} {x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (A : TorusAt X x)
    (q n : ℕ) (π : Vsp A.T.dim →ₗ[ℂ] Vsp A.T.dim) (hπ : IsPi A.T q π)
    (b : Fin n → Vsp A.T.dim) (P : MvPolynomial (Letter n A.T.dim) ℂ) (a : ℕ)
    (hP : P.IsHomogeneous a) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ γ ∈ A.T.L, γ ≠ 0 → lam ≤ ‖γ‖) :
    ‖thAn A q n π b P‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx A.T.dim)) /
          (Real.sqrt Real.pi * lam)) ^ Fintype.card (Idx A.T.dim)) ^ n := by sorry
