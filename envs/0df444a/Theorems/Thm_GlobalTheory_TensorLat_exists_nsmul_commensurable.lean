-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_exists_nsmul_commensurable
-- name    : GlobalTheory.TensorLat.exists_nsmul_commensurable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:32:23.67874+00:00
-- url     : https://prove2.me/theorems/2a7bcbf2-de28-54fd-b5d9-11ba80027fe0
-- title:
--   Tensor Lat: exists nsmul commensurable
-- statement:
--   The Tensor Lat construction uses the exists nsmul commensurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NsmulApplyMemOfMemTensorLat.lean#L172-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NsmulApplyMemOfMemTensorLat.lean#L172-L180

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

theorem GlobalTheory.TensorLat.exists_nsmul_commensurable (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') :
    ∃ M : ℕ, 1 ≤ M ∧
      (∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → M • γ ∈ tensorLat X Λ') ∧
      (∀ γ ∈ tensorLat X Λ', ∀ k, (M • γ) k ∈ X.L) := by sorry
