-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_lat_bdd
-- name    : GlobalTheory.CompanionTheory.RgSplit.lat_bdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:10.021984+00:00
-- url     : https://prove2.me/theorems/50a5ffe1-38c2-414f-8c68-cb8ec0a7b152
-- title:
--   Rg Split: lat bdd
-- statement:
--   The Rg Split construction uses the lat bdd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L48-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L48-L60

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

theorem GlobalTheory.CompanionTheory.RgSplit.lat_bdd {V' : Type} [AddCommGroup V'] [Module L V'] {Λ : AddSubgroup V}
    {Λ₀ : AddSubgroup V'} (hΛ : IsLat L Λ) (hΛ₀ : IsLat L Λ₀) (P : V →ₗ[L] V') :
    ∃ c : L, c ≠ 0 ∧ ‖c‖ ≤ 1 ∧ ∀ x ∈ Λ, c • P x ∈ Λ₀ := by sorry
