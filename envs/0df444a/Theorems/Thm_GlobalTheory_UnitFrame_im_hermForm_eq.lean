-- Prove2me | Theorems.Thm_GlobalTheory_UnitFrame_im_hermForm_eq
-- name    : GlobalTheory.UnitFrame.im_hermForm_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:06.366663+00:00
-- url     : https://prove2.me/theorems/61b65145-8394-4c38-b394-1c2adb3d217a
-- title:
--   Unit Frame: im herm Form eq
-- statement:
--   The Unit Frame construction uses the im herm Form eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemIffConjugateNotMem.lean#L187-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemIffConjugateNotMem.lean#L187-L232

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemIffConjugateNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnitFrame
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.UnitFrame.im_hermForm_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ y))) → ∀ (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (P : D.La →+ (Fin g → ℂ)), (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → (∀ τ : Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn D.q (a : ℕ) : ℝ) : ℂ)) → ∀ v w, (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm (Matrix.diagonal fun k => ((2 * ‖(idx k).1.1 ξ‖ : ℝ) : ℂ)) (P v) (P w)).im = D.EF v w := by sorry
