-- Prove2me | Theorems.Thm_GlobalTheory_per_move
-- name    : GlobalTheory.per_move
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:44:02.922682+00:00
-- url     : https://prove2.me/theorems/3046c775-872b-450a-a1a8-5bb8a8d455a7
-- title:
--   Global Theory: per move
-- statement:
--   The Global Theory construction uses the per move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L256-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L256-L398

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.per_move :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
        : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D
        : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (r : ℕ) (ξ : E) (Gm
        : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ
        : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+*
        ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx
        k).1.1 else (idx
        k).1.1), _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ
        ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧
        (∀ a b, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧
        ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ *
        _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm (φ x) (φ
        y))) → (∀ P : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r → (D.La →+ (Fin g →
        ℂ)), (∀ x, (∀ v k, P x v k = if ((idx k).2
        : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2)) → ∀ v, DifferentiableOn ℂ (fun x => P x v) (_root_.ReciprocityTheory.ChartRestriction.G.FD.GG
        Ψ Gm D.q)) ∧ (∀ (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (γ : GL (Fin
        r) E) (P P' : D.La →+ (Fin g →
        ℂ)), (∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm ((γ : Matrix (Fin
        r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ
        v) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm Gm u v) → (∀ v k, P v k = if ((idx
        k).2 : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2) → (∀ v k, P' v k = if ((idx k).2
        : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.lact γ x) (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2) → ∀ v v', φ v' = (γ : Matrix (Fin r) (Fin
        r) E) *ᵥ φ v → P' v' = P v) ∧ ∀ x ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ Gm D.q, ∀ b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r, ∀ (P
        P' : D.La →+ (Fin g → ℂ)), (∀ v k, P v k = if ((idx k).2
        : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2) → (∀ v k, P' v k = if ((idx k).2
        : ℕ) < D.q then _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (idx
        k).1.1 Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.col
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) (idx k).1) (idx
        k).2) (_root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ
        v)) else ((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat
        (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) (idx k).1)⁻¹ *ᵥ
        _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.emb (idx k).1.1 (φ v)) (idx
        k).2) → _root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.GG Ψ Gm D.q ∧ ∃ h : Matrix (Fin
        g) (Fin g) ℂ, (∀ v, P' v = h *ᵥ P v) ∧ (∀ k, h k k = if ((idx k).2 : ℕ) < D.q then b (idx
        k).1 (idx k).2 (idx k).2 else (b (idx k).1 (idx k).2 (idx
        k).2)⁻¹) ∧ h.det = ∏ k, h k k := by sorry
