-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_isogeny_sum_tensorLat
-- name    : GlobalTheory.TensorLat.isogeny_sum_tensorLat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:33:44.117803+00:00
-- url     : https://prove2.me/theorems/e3b432cc-5742-57d9-b43b-bcc3bba3ddbf
-- title:
--   Tensor Lat: isogeny sum tensor Lat
-- statement:
--   The Tensor Lat construction uses the isogeny sum tensor Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormalisedThetaValueBound.lean#L18-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NormalisedThetaValueBound.lean#L18-L69

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

theorem GlobalTheory.TensorLat.isogeny_sum_tensorLat (T : PT E) (w₀ : 𝓞 E) (hw : (w₀ : E) + cc (w₀ : E) = 1)
    (heps : ∀ x ∈ T.L, (T.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    (Λ' : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    (R : Finset (Fin n → Vsp T.dim)) (hR : ∀ y ∈ R, y ∈ tensorLat T Λ')
    (hR' : ∀ y ∈ tensorLat T Λ', ∃! r, r ∈ R ∧ ∀ k, y k - r k ∈ T.L)
    (F : (Fin n → Vsp T.dim) → ℂ) (hF : F ∈ T.Sec 1 n)
    (Y' : GT (Fin n × Idx T.dim)) (hY' : ∀ γ, flat γ ∈ lat Y'.b ↔ γ ∈ tensorLat T Λ')
    (hka' : ∀ γ, Y'.ka (flat γ) = tensorEps w₀ γ) :
    (∑ y ∈ R, tensorEps w₀ y • T.U 1 y F) ∘ flat.symm ∈ Y'.Sec 1 ∧
      Y'.l2 1 ((∑ y ∈ R, tensorEps w₀ y • T.U 1 y F) ∘ flat.symm) = R.card * T.l2 1 F := by sorry
