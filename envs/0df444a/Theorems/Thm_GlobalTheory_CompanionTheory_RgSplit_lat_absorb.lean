-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_lat_absorb
-- name    : GlobalTheory.CompanionTheory.RgSplit.lat_absorb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:54:59.742827+00:00
-- url     : https://prove2.me/theorems/80d47ddd-369d-4b47-8612-2b1ebc898429
-- title:
--   Rg Split: lat absorb
-- statement:
--   The Rg Split construction uses the lat absorb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L22-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L22-L46

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

theorem GlobalTheory.CompanionTheory.RgSplit.lat_absorb {Λ : AddSubgroup V} (hΛ : IsLat L Λ) {ι : Type} [Fintype ι] (v : ι → V) :
    ∃ c : L, c ≠ 0 ∧ ‖c‖ ≤ 1 ∧ ∀ i, c • v i ∈ Λ := by sorry
