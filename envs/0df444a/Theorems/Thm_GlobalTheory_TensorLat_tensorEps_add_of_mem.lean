-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_tensorEps_add_of_mem
-- name    : GlobalTheory.TensorLat.tensorEps_add_of_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T17:19:07.326844+00:00
-- url     : https://prove2.me/theorems/18855d16-5b43-55ad-a8f1-cb3c2583ced1
-- title:
--   Tensor Lat: tensor Eps add of mem
-- statement:
--   The Tensor Lat construction uses the tensor Eps add of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsBasisSpanEqOfCommensurable.lean#L250-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsBasisSpanEqOfCommensurable.lean#L250-L264

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
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
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable [IsCMField E]
variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}

theorem GlobalTheory.TensorLat.tensorEps_add_of_mem (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') (w₀ : 𝓞 E)
    (hw : (w₀ : E) + cc (w₀ : E) = 1) {γ δ : Fin n → Vsp X.dim}
    (hγ : γ ∈ tensorLat X Λ') (hδ : δ ∈ tensorLat X Λ') :
    tensorEps w₀ (γ + δ) =
      tensorEps w₀ γ * tensorEps w₀ δ * cexp (Real.pi * I * (HC γ δ).im) := by sorry
