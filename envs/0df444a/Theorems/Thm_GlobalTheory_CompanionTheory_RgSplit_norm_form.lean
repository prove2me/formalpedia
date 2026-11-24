-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_norm_form
-- name    : GlobalTheory.CompanionTheory.RgSplit.norm_form
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:41.869557+00:00
-- url     : https://prove2.me/theorems/369bec80-af4a-42a6-b6d9-58ef3c5ddf26
-- title:
--   Rg Split: norm form
-- statement:
--   The Rg Split construction uses the norm form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L172-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L172-L180

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
variable {δ : L} {e f : V}

theorem GlobalTheory.CompanionTheory.RgSplit.norm_form (hs : IsInv s) (hh : IsHerm s h) (he : h e e = 0) (hf : h f f = 0)
    (hef : h e f = δ) (a b : L) {w : V} (hew : h e w = 0) (hfw : h f w = 0) :
    h (a • e + b • f + w) (a • e + b • f + w) = δ * (s a * b) + s (δ * (s a * b)) + h w w := by sorry
