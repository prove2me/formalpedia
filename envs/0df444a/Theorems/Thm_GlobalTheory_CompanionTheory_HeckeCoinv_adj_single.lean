-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_adj_single
-- name    : GlobalTheory.CompanionTheory.HeckeCoinv.adj_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:45:46.814391+00:00
-- url     : https://prove2.me/theorems/8a88dc72-e79f-46df-9a0b-b3b3707bdaf6
-- title:
--   Hecke Coinv: adj single
-- statement:
--   The Hecke Coinv construction uses the adj single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L233-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L233-L257

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

theorem GlobalTheory.CompanionTheory.HeckeCoinv.adj_single {N : ℕ} (Γ : Subgroup G) [∀ x : G ⧸ K, Finite (MulAction.stabilizer Γ x)]
    (hp : IsHeckePair K) (h : Hk K) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hφ : ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ)) (x y : G ⧸ K) :
    ⟪φ (Finsupp.single x 1), φ (h.1 (Finsupp.single y 1))⟫_ℂ =
      ⟪φ ((starH hp h).1 (Finsupp.single x 1)), φ (Finsupp.single y 1)⟫_ℂ := by sorry
