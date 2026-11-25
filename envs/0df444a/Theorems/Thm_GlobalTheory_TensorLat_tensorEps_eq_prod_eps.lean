-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_tensorEps_eq_prod_eps
-- name    : GlobalTheory.TensorLat.tensorEps_eq_prod_eps
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:30:11.515958+00:00
-- url     : https://prove2.me/theorems/1246c23d-b3c3-4144-9a41-f57fa67e261b
-- title:
--   Tensor Lat: tensor Eps eq prod eps
-- statement:
--   The Tensor Lat construction uses the tensor Eps eq prod eps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/FlatMemLatIffStdLat.lean#L213-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/FlatMemLatIffStdLat.lean#L213-L223

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ActEMemSpanOmega
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
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
noncomputable section
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}

theorem GlobalTheory.TensorLat.tensorEps_eq_prod_eps (X : PT E) (w₀ : 𝓞 E)
    (heps : ∀ x ∈ X.L, (X.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) :
    tensorEps w₀ γ = ∏ k, (X.eps (γ k) : ℂ) := by sorry
