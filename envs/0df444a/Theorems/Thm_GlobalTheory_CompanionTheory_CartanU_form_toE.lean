-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartanU_form_toE
-- name    : GlobalTheory.CompanionTheory.CartanU.form_toE
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:30:54.901844+00:00
-- url     : https://prove2.me/theorems/142bc393-e071-4ad1-9f1a-71e1e9b8c4de
-- title:
--   Cartan U: form to E
-- statement:
--   The Cartan U construction uses the form to E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean#L64-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/IsometricLatticeCongruenceSubgroups.lean#L64-L71

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

theorem GlobalTheory.CompanionTheory.CartanU.form_toE (s : L →+* L) (J : Matrix (Fin n) (Fin n) L) (g : GL (Fin n) L) (x y : Fin n → L) :
    form s J (toE g x) (toE g y) = dotProduct (s ∘ x) (((g.1.map s).transpose * J * g.1).mulVec y) := by sorry
