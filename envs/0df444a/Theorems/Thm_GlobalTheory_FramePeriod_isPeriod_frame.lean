-- Prove2me | Theorems.Thm_GlobalTheory_FramePeriod_isPeriod_frame
-- name    : GlobalTheory.FramePeriod.isPeriod_frame
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:02.547739+00:00
-- url     : https://prove2.me/theorems/bdf77975-723e-4400-b7cd-ec0ceb8dde95
-- title:
--   Frame Period: is Period frame
-- statement:
--   The Frame Period construction uses the is Period frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L365-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HermFormConjDiag.lean#L365-L454

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermFormConjDiag
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
open GlobalTheory GlobalTheory.FramePeriod
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.FramePeriod.isPeriod_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = D.p + D.q → IsTypeFn H D.p D.q ty ∧ ∀ x ∈ FD.GG Ψ Gm D.q, (∃ P : D.La →+ (Fin g → ℂ), (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2)) ∧ ∀ P : D.La →+ (Fin g → ℂ), (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → IsPeriod D ty P := by sorry
