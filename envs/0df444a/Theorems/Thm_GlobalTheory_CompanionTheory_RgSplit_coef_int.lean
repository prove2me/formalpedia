-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_coef_int
-- name    : GlobalTheory.CompanionTheory.RgSplit.coef_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:11.05986+00:00
-- url     : https://prove2.me/theorems/995f7487-de78-4312-b512-31f6491be7ea
-- title:
--   Rg Split: coef int
-- statement:
--   The Rg Split construction uses the coef int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L189-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L189-L202

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

theorem GlobalTheory.CompanionTheory.RgSplit.coef_int (hs : IsInv s) (hδ : δ ≠ 0) (hh : IsHerm s h) {Λ : AddSubgroup V}
    (hΛ : IsLat L Λ) (hpair : ∀ x ∈ Λ, ∀ y ∈ Λ, ‖h x y‖ ≤ ‖δ‖) (heΛ : e ∈ Λ) (hfΛ : f ∈ Λ)
    {x : V} (hx : x ∈ Λ) :
    ‖ca hh δ f x‖ ≤ 1 ∧ ‖cb hh δ e x‖ ≤ 1 ∧ pr hh δ e f x ∈ Λ := by sorry
