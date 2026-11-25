-- Prove2me | Theorems.Thm_GlobalTheory_exists_frame_of_isPeriod
-- name    : GlobalTheory.exists_frame_of_isPeriod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:38:59.718901+00:00
-- url     : https://prove2.me/theorems/88ed5147-9551-47c9-a486-887197baea5e
-- title:
--   Global Theory: exists frame of is Period
-- statement:
--   The Global Theory construction uses the exists frame of is Period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L446-L491
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsFrameOfIsPeriod.lean#L446-L491

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqIffConjNe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFrameOfIsPeriod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open PeriodOnto

theorem GlobalTheory.exists_frame_of_isPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (_hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (g : ℕ) (idx : Fin g ≃ Ψ × Fin r) (ty : Fin g → (E →+* ℂ)) (_hty : ∀ k, ty k = if ((idx k).2 : ℕ) < D.q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1), FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = D.p + D.q → ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D ty P → ∃ x ∈ FD.GG Ψ Gm D.q, (∀ v k, P v k = if ((idx k).2 : ℕ) < D.q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) := by sorry
