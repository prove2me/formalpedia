-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_add_left
-- name    : GlobalTheory.CompanionTheory.HermAniso.add_left
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:23.110884+00:00
-- url     : https://prove2.me/theorems/181af35a-8fb5-40c0-88e2-c96d4d4c0475
-- title:
--   Herm Aniso: add left
-- statement:
--   The Herm Aniso construction uses the add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AnisotropicOfHenselAndSandwich.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AnisotropicOfHenselAndSandwich.lean#L15-L17

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AnisotropicOfHenselAndSandwich
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermAniso
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem GlobalTheory.CompanionTheory.HermAniso.add_left (hh : IsHerm s h) (x y z : V) : h (x + y) z = h x z + h y z := by sorry
