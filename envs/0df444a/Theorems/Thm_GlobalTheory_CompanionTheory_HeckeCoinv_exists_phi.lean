-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_exists_phi
-- name    : GlobalTheory.CompanionTheory.HeckeCoinv.exists_phi
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:45:50.343943+00:00
-- url     : https://prove2.me/theorems/2e7126e8-54da-4326-afda-3da891847f07
-- title:
--   Hecke Coinv: exists phi
-- statement:
--   The Hecke Coinv construction uses the exists phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L79-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L79-L137

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCoinv
variable (Γ : Type) {X : Type} [Group Γ] [MulAction Γ X]
variable {Γ}

theorem GlobalTheory.CompanionTheory.HeckeCoinv.exists_phi [Finite (MulAction.orbitRel.Quotient Γ X)] [∀ x : X, Finite (MulAction.stabilizer Γ x)] :
    ∃ (N : ℕ) (φ : (X →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N)), Function.Surjective φ ∧
      ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ) := by sorry
