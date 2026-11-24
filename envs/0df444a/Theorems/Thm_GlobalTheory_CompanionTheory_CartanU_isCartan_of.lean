-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_isCartan_of
-- name    : GlobalTheory.CompanionTheory.CartanU.isCartan_of
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:31:02.847057+00:00
-- url     : https://prove2.me/theorems/85e87550-3703-48c1-9e15-34765e8457c2
-- title:
--   Cartan U: is Cartan of
-- statement:
--   The Cartan U construction uses the is Cartan of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean#L223-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean#L223-L244

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsometricLatticeCongruenceSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartanU

theorem GlobalTheory.CompanionTheory.CartanU.isCartan_of {G : Type} [Group G] (K K₀ : Subgroup G) {d l : ℕ} (T : (Fin l → ℕ) → G)
    (h0 : T 0 = 1) (hadd : ∀ a b, T (a + b) = T a * T b) (c : Fin d → G) (hc : ∀ i, c i ∈ K₀)
    (hcov : ∀ g ∈ K₀, ∃ i, ∃ k ∈ K, g = c i * k)
    (hnorm : ∀ c ∈ K₀, ∀ k, k ∈ K ↔ c * k * c⁻¹ ∈ K)
    (hdec : ∀ g, ∃ k ∈ K₀, ∃ k' ∈ K₀, ∃ r : Fin l → ℕ, Antitone r ∧ g = k * T r * k')
    (hiw : ∀ k ∈ K, ∃ a b : G, k = a * b ∧ ∀ r : Fin l → ℕ, Antitone r →
      T r * a * (T r)⁻¹ ∈ K ∧ (T r)⁻¹ * b * T r ∈ K) :
    IsCartan K d l := by sorry
