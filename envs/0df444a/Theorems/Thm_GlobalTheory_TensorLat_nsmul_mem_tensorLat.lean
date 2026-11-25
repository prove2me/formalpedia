-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_nsmul_mem_tensorLat
-- name    : GlobalTheory.TensorLat.nsmul_mem_tensorLat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:32:28.988275+00:00
-- url     : https://prove2.me/theorems/c0761583-e969-5dc0-a566-3d439e1d34f2
-- title:
--   Tensor Lat: nsmul mem tensor Lat
-- statement:
--   The Tensor Lat construction uses the nsmul mem tensor Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NsmulApplyMemOfMemTensorLat.lean#L101-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NsmulApplyMemOfMemTensorLat.lean#L101-L112

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

theorem GlobalTheory.TensorLat.nsmul_mem_tensorLat (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) {N : ℕ}
    (hN : ∀ u ∈ stdLat E n, N • u ∈ Λ') {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) :
    N • γ ∈ tensorLat X Λ' := by sorry
