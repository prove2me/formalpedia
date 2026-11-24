-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_mem_UG_iff
-- name    : GlobalTheory.CompanionTheory.CartanU.mem_UG_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:09.433878+00:00
-- url     : https://prove2.me/theorems/b218ac95-eb3f-4c91-aa55-b3cbe9691d5b
-- title:
--   Cartan U: mem UG iff
-- statement:
--   The Cartan U construction uses the mem UG iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean#L73-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean#L73-L90

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

theorem GlobalTheory.CompanionTheory.CartanU.mem_UG_iff (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (g : GL (Fin n) L) :
    g ∈ UG s J ↔ IsIso (form s J) (toE g) := by sorry
