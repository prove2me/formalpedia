-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_im_HC_int
-- name    : GlobalTheory.TensorLat.im_HC_int
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:34:34.662895+00:00
-- url     : https://prove2.me/theorems/173365c8-7011-476a-951d-1a85117c6358
-- title:
--   Tensor Lat: im HC int
-- statement:
--   The Tensor Lat construction uses the im HC int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NsmulApplyMemOfMemTensorLat.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NsmulApplyMemOfMemTensorLat.lean#L52-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}

theorem GlobalTheory.TensorLat.im_HC_int (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ')
    {γ γ' : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') (hγ' : γ' ∈ tensorLat X Λ') :
    ∃ k : ℤ, (HC γ γ').im = k := by sorry
