-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_pair_le
-- name    : GlobalTheory.CompanionTheory.HermAniso.pair_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:00.421909+00:00
-- url     : https://prove2.me/theorems/36aabd1e-0df7-42ae-bf5b-bdf26f2ba260
-- title:
--   Herm Aniso: pair le
-- statement:
--   The Herm Aniso construction uses the pair le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AnisotropicOfHenselAndSandwich.lean#L31-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AnisotropicOfHenselAndSandwich.lean#L31-L77

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

theorem GlobalTheory.CompanionTheory.HermAniso.pair_le [IsUltrametricDist L] [CompleteSpace L] (hH : StHensel) (hs : IsInv s) (hh : IsHerm s h)
    (hani : ∀ x, h x x = 0 → x = 0) {x y : V} (hx : ‖h x x‖ ≤ 1) (hy : ‖h y y‖ ≤ 1) :
    ‖h x y + h y x‖ ≤ 1 := by sorry
