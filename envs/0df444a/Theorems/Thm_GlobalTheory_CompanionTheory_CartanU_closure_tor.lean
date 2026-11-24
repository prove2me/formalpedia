-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_closure_tor
-- name    : GlobalTheory.CompanionTheory.CartanU.closure_tor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:35.835246+00:00
-- url     : https://prove2.me/theorems/9ab62935-71c2-4622-abbb-985358d6f383
-- title:
--   Cartan U: closure tor
-- statement:
--   The Cartan U construction uses the closure tor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean#L152-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean#L152-L221

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

theorem GlobalTheory.CompanionTheory.CartanU.closure_tor {M : Type} [Monoid M] {l : ℕ} (T : (Fin l → ℕ) → M) (h0 : T 0 = 1)
    (hadd : ∀ a b, T (a + b) = T a * T b) (g : M) :
    g ∈ Submonoid.closure (Set.range fun i : Fin l => T (ind i)) ↔
      ∃ r : Fin l → ℕ, Antitone r ∧ g = T r := by sorry
