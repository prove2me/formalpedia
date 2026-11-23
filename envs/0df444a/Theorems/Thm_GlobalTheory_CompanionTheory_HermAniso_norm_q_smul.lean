-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_norm_q_smul
-- name    : GlobalTheory.CompanionTheory.HermAniso.norm_q_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:42.061878+00:00
-- url     : https://prove2.me/theorems/f59aa26b-2d17-4a38-88ab-112e8edcfc48
-- title:
--   Herm Aniso: norm q smul
-- statement:
--   The Herm Aniso construction uses the norm q smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AnisotropicOfHenselAndSandwich.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AnisotropicOfHenselAndSandwich.lean#L27-L29

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

theorem GlobalTheory.CompanionTheory.HermAniso.norm_q_smul (hs : IsInv s) (hh : IsHerm s h) (a : L) (x : V) :
    ‖h (a • x) (a • x)‖ = ‖a‖ * ‖a‖ * ‖h x x‖ := by sorry
