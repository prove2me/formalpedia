-- Prove2me | Theorems.Thm_GlobalTheory_TensorLat_tensorLat_span_integral_perfect
-- name    : GlobalTheory.TensorLat.tensorLat_span_integral_perfect
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:39:57.580891+00:00
-- url     : https://prove2.me/theorems/3b80c1d2-5a57-4f4c-a762-7882f334358d
-- title:
--   Tensor Lat: tensor Lat span integral perfect
-- statement:
--   The Tensor Lat construction uses the tensor Lat span integral perfect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NsmulApplyMemOfMemTensorLat.lean#L182-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/NsmulApplyMemOfMemTensorLat.lean#L182-L209

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

theorem GlobalTheory.TensorLat.tensorLat_span_integral_perfect (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E))
    (hfg : Λ'.FG) (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') :
    (∃ (m : ℕ) (v w : Fin m → Fin n → E), (∀ i, v i ∈ Λ') ∧ (∀ i, w i ∈ Λ') ∧
      (∀ u : Fin n → E, u = ∑ i, herm 1 u (w i) • v i) ∧
      ∀ γ : Fin n → Vsp X.dim, γ = ∑ i, tens (contr γ (w i)) (v i)) ∧
    (∀ (m : ℕ) (v w : Fin m → Fin n → E), (∀ u : Fin n → E, u = ∑ i, herm 1 u (w i) • v i) →
      ∀ γ : Fin n → Vsp X.dim, γ = ∑ i, tens (contr γ (w i)) (v i)) ∧
    tensorLat X Λ' = Submodule.span ℤ {γ | ∃ x ∈ X.L, ∃ v ∈ Λ', γ = tens x v} ∧
    (∀ (α : 𝓞 E), ∀ γ ∈ tensorLat X Λ', (fun k => act α (γ k)) ∈ tensorLat X Λ') ∧
    (∀ γ ∈ tensorLat X Λ', ∀ γ' ∈ tensorLat X Λ', ∃ k : ℤ, (HC γ γ').im = k) ∧
    (∀ φ : tensorLat X Λ' →+ ℤ, ∃ γ ∈ tensorLat X Λ', ∀ γ' : tensorLat X Λ',
      (φ γ' : ℝ) = (HC γ (γ' : Fin n → Vsp X.dim)).im) ∧
    (∃ N : ℕ, 1 ≤ N ∧ ∀ u ∈ stdLat E n, N • u ∈ Λ') ∧
    (∀ N : ℕ, (∀ u ∈ stdLat E n, N • u ∈ Λ') →
      (∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → N • γ ∈ tensorLat X Λ') ∧
      (∀ γ ∈ tensorLat X Λ', ∀ k, (N • γ) k ∈ X.L)) ∧
    (∃ M : ℕ, 1 ≤ M ∧
      (∀ γ : Fin n → Vsp X.dim, (∀ k, γ k ∈ X.L) → M • γ ∈ tensorLat X Λ') ∧
      (∀ γ ∈ tensorLat X Λ', ∀ k, (M • γ) k ∈ X.L)) := by sorry
