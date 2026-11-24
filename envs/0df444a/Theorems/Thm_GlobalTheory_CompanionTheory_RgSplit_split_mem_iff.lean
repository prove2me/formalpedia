-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_split_mem_iff
-- name    : GlobalTheory.CompanionTheory.RgSplit.split_mem_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:58.342637+00:00
-- url     : https://prove2.me/theorems/48b5aa7e-110c-4895-a4d6-ae7d90a547c7
-- title:
--   Rg Split: split mem iff
-- statement:
--   The Rg Split construction uses the split mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L295-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L295-L306

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
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L]
  {V : Type} [AddCommGroup V] [Module L V] {s : L →+* L} {h : V → V → L} {δ : L} {e f : V}
variable {U : Submodule L V}

theorem GlobalTheory.CompanionTheory.RgSplit.split_mem_iff (hs : IsInv s) (hδ : δ ≠ 0) (hh : IsHerm s h) (he : h e e = 0)
    (hf : h f f = 0) (hef : h e f = δ) {Λ : AddSubgroup V} (hΛ : IsLat L Λ)
    (hpair : ∀ x ∈ Λ, ∀ y ∈ Λ, ‖h x y‖ ≤ ‖δ‖) (heΛ : e ∈ Λ) (hfΛ : f ∈ Λ) (a b : L) {w : V}
    (hew : h e w = 0) (hfw : h f w = 0) :
    a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ w ∈ Λ := by sorry
