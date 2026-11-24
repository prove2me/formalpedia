-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_restrict_isMax
-- name    : GlobalTheory.CompanionTheory.RgSplit.restrict_isMax
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:58.646042+00:00
-- url     : https://prove2.me/theorems/70f292f4-b087-47ff-9c63-08686e3cddb0
-- title:
--   Rg Split: restrict is Max
-- statement:
--   The Rg Split construction uses the restrict is Max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L240-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L240-L293

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

theorem GlobalTheory.CompanionTheory.RgSplit.restrict_isMax (hS : StSandwich) [ProperSpace L] [FiniteDimensional L V] (hs : IsInv s)
    (hδ : IsDelta s δ) (hh : IsHerm s h) (he : h e e = 0) (hf : h f f = 0) (hef : h e f = δ)
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) {Λ : AddSubgroup V} (hΛ : IsMax h Λ)
    (hpair : ∀ x ∈ Λ, ∀ y ∈ Λ, ‖h x y‖ ≤ ‖δ‖) (heΛ : e ∈ Λ) (hfΛ : f ∈ Λ) :
    IsMax (fun x y : U => h x y) (Λ.comap U.subtype.toAddMonoidHom) := by sorry
