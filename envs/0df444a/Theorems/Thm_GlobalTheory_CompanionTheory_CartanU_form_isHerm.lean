-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_form_isHerm
-- name    : GlobalTheory.CompanionTheory.CartanU.form_isHerm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:30:47.996834+00:00
-- url     : https://prove2.me/theorems/cd52afac-98a4-4672-a752-277a0eab3c3e
-- title:
--   Cartan U: form is Herm
-- statement:
--   The Cartan U construction uses the form is Herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean#L18-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean#L18-L38

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

theorem GlobalTheory.CompanionTheory.CartanU.form_isHerm (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (hs : ∀ x, s (s x) = x)
    (hJ : (J.map s).transpose = J) (hd : J.det ≠ 0) : IsHerm s (form s J) := by sorry
