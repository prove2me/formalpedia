-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_inner_phi
-- name    : GlobalTheory.CompanionTheory.HeckeCoinv.inner_phi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:46.402422+00:00
-- url     : https://prove2.me/theorems/32ea53b3-648b-451b-99c2-405ab6ea80e1
-- title:
--   Hecke Coinv: inner phi
-- statement:
--   The Hecke Coinv construction uses the inner phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L220-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ModularityStatement.lean#L220-L231

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

theorem GlobalTheory.CompanionTheory.HeckeCoinv.inner_phi {N : ℕ} (Γ : Subgroup G) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hφ : ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ))
    (x : G ⧸ K) (f : (G ⧸ K) →₀ ℂ) :
    ⟪φ (Finsupp.single x 1), φ f⟫_ℂ = f.sum fun z c => c * (cnt Γ x z : ℂ) := by sorry
