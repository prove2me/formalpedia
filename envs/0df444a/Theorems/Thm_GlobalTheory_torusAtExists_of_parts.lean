-- Prove2me | Theorems.Thm_GlobalTheory_torusAtExists_of_parts
-- name    : GlobalTheory.torusAtExists_of_parts
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:12:36.372908+00:00
-- url     : https://prove2.me/theorems/f326c2b2-802f-422e-bc6d-a1e14752840a
-- title:
--   Global Theory: torus At Exists of parts
-- statement:
--   The Global Theory construction uses the torus At Exists of parts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TorusAtExistsOfParts.lean#L171-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TorusAtExistsOfParts.lean#L171-L319

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TorusAtExistsOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open NumberField
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.torusAtExists_of_parts :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∀ x ∈ X.dom, ∃ e : X.Ψ → Fin r → (Fin r → ℂ), (∀ τ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) ∧ ∀ τ (i : ℕ) (hi : i ≤ r), Submodule.span ℂ (Set.range fun a : Fin i => e τ (Fin.castLE hi a)) = Submodule.span ℂ (Set.range fun a : Fin i => _root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (Fin.castLE hi a))) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ b : Module.Basis (Fin (2 * (X.Ψ.card * r))) ℝ (X.Ψ → Fin r → ℂ), ∀ y, y ∈ Submodule.span ℤ (Set.range b) ↔ ∃ v ∈ X.Λ, (fun τ : X.Ψ => _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v) = y) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧ ∀ u v : Fin r → E, ∑ τ : X.Ψ, X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 u) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)).im = sg * ((Algebra.trace ℚ E (X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v) : ℚ) : ℝ)) → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ)), (∀ τ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (e τ a) (e τ b) = if a = b then ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) → ∃ (dim : (E →+* ℂ) → ℕ) (hp : ∀ τ : X.Ψ, dim τ.1 = X.p0) (hn : ∀ τ : X.Ψ, dim (ComplexEmbedding.conjugate τ.1) = r - X.p0) (Φ : (X.Ψ → Fin r → ℂ) ≃ₗ[ℝ] _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp dim), Fintype.card (_root_.ReciprocityTheory.ChartRestriction.G.I2.Idx dim) = X.Ψ.card * r ∧ (∀ τ, dim τ + dim (ComplexEmbedding.conjugate τ) = r) ∧ (∀ y (τ : X.Ψ) (a : Fin (dim τ.1)), (Φ y) ⟨τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ (Fin.castLE (by rw [hp τ]; exact X.p0_le) a))) ∧ (∀ y (τ : X.Ψ) (a : Fin (dim (ComplexEmbedding.conjugate τ.1))), (Φ y) ⟨ComplexEmbedding.conjugate τ.1, a⟩ = (Real.sqrt (X.c τ) : ℂ) * (starRingEnd ℂ) (-_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (e τ ⟨X.p0 + a.1, by have h1 : a.1 < r - X.p0 := lt_of_lt_of_eq a.2 (hn τ); have := X.p0_le; omega⟩))) ∧ (∀ (α : 𝓞 E) y, Φ (fun τ => τ.1 (α : E) • y τ) = _root_.ReciprocityTheory.ChartRestriction.G.I2.act α (Φ y)) ∧ ∀ y y', (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (Φ y) (Φ y')).im = ∑ τ : X.Ψ, X.c τ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.hermC τ.1 X.Gm (y τ) (y' τ)).im) → (∀ (E : Type) [Field E] [NumberField E] (X : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E), ∃ s ∈ X.Sec 1 1, s ≠ 0) → _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtExistsStatement := by sorry
