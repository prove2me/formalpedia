-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_toE_surj
-- name    : GlobalTheory.CompanionTheory.CartanU.toE_surj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:31:32.479801+00:00
-- url     : https://prove2.me/theorems/efdd362b-8cf8-4155-9040-648d0a2f4e95
-- title:
--   Cartan U: to E surj
-- statement:
--   The Cartan U construction uses the to E surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean#L92-L94

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
variable {L : Type} [NontriviallyNormedField L] {n : ℕ}

theorem GlobalTheory.CompanionTheory.CartanU.toE_surj (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (t : (Fin n → L) ≃ₗ[L] (Fin n → L))
    (ht : IsIso (form s J) t) : ∃ g : UG s J, toE g.1 = t := by sorry
