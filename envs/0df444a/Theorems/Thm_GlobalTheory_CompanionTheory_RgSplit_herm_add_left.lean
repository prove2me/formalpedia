-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_herm_add_left
-- name    : GlobalTheory.CompanionTheory.RgSplit.herm_add_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:24.245796+00:00
-- url     : https://prove2.me/theorems/4edf8247-62fe-45ea-b992-a75ecf5eef9a
-- title:
--   Rg Split: herm add left
-- statement:
--   The Rg Split construction uses the herm add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L101-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L101-L102

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgSplit
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

theorem GlobalTheory.CompanionTheory.RgSplit.herm_add_left (hh : IsHerm s h) (x y z : V) : h (x + y) z = h x z + h y z := by sorry
