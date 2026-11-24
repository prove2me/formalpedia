-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_exists_rho
-- name    : GlobalTheory.CompanionTheory.HeckeCoinv.exists_rho
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:46:19.471268+00:00
-- url     : https://prove2.me/theorems/787143ad-1c31-4bd2-a4d7-a9a7f36e39b5
-- title:
--   Hecke Coinv: exists rho
-- statement:
--   The Hecke Coinv construction uses the exists rho property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L281-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L281-L322

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
variable {G : Type} [Group G] {K : Subgroup G}

theorem GlobalTheory.CompanionTheory.HeckeCoinv.exists_rho {N : ℕ} (hp : IsHeckePair K) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hs : Function.Surjective φ)
    (hadj : ∀ (h : Hk K) u v, ⟪φ u, φ (h.1 v)⟫_ℂ = ⟪φ ((starH hp h).1 u), φ v⟫_ℂ) :
    ∃ ρ : Hk K →ₐ[ℂ] Module.End ℂ (EuclideanSpace ℂ (Fin N)),
      StarClosed ρ ∧ ∀ h u, ρ h (φ u) = φ (h.1 u) := by sorry
