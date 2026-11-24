-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_exists_ball
-- name    : GlobalTheory.CompanionTheory.HermAniso.exists_ball
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:11.365807+00:00
-- url     : https://prove2.me/theorems/527d492e-0f8c-4544-8cf6-06053e90179c
-- title:
--   Herm Aniso: exists ball
-- statement:
--   The Herm Aniso construction uses the exists ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AnisotropicOfHenselAndSandwich.lean#L79-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AnisotropicOfHenselAndSandwich.lean#L79-L95

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

theorem GlobalTheory.CompanionTheory.HermAniso.exists_ball [IsUltrametricDist L] (hs : IsInv s) (hh : IsHerm s h)
    (hp : ∀ x y : V, ‖h x x‖ ≤ 1 → ‖h y y‖ ≤ 1 → ‖h x y + h y x‖ ≤ 1) :
    ∃ V₀ : AddSubgroup V, ∀ x, x ∈ V₀ ↔ ‖h x x‖ ≤ 1 := by sorry
