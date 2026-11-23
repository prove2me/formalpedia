-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_coef_eq
-- name    : GlobalTheory.CompanionTheory.RgSplit.coef_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:55:12.282398+00:00
-- url     : https://prove2.me/theorems/14c805f6-8515-41ee-98e4-fe7fd8195604
-- title:
--   Rg Split: coef eq
-- statement:
--   The Rg Split construction uses the coef eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L154-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L154-L170

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

theorem GlobalTheory.CompanionTheory.RgSplit.coef_eq (hh : IsHerm s h) (hδ : δ ≠ 0) (he : h e e = 0) (hf : h f f = 0)
    (hef : h e f = δ) (a b : L) {w : V} (hew : h e w = 0) (hfw : h f w = 0) :
    ca hh δ f (a • e + b • f + w) = a ∧ cb hh δ e (a • e + b • f + w) = b ∧
      pr hh δ e f (a • e + b • f + w) = w := by sorry
