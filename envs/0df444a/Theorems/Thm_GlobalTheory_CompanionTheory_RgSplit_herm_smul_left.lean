-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_herm_smul_left
-- name    : GlobalTheory.CompanionTheory.RgSplit.herm_smul_left
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:30.165971+00:00
-- url     : https://prove2.me/theorems/cca64a66-ef02-4a0a-a663-3d85abf79426
-- title:
--   Rg Split: herm smul left
-- statement:
--   The Rg Split construction uses the herm smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L104-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L104-L105

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

theorem GlobalTheory.CompanionTheory.RgSplit.herm_smul_left (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by sorry
