-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_restrict_isLat
-- name    : GlobalTheory.CompanionTheory.RgSplit.restrict_isLat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:50.218319+00:00
-- url     : https://prove2.me/theorems/a98bfa0b-1740-4e26-9a98-3b80cd55fc72
-- title:
--   Rg Split: restrict is Lat
-- statement:
--   The Rg Split construction uses the restrict is Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L222-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L222-L238

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

theorem GlobalTheory.CompanionTheory.RgSplit.restrict_isLat (hS : StSandwich) [ProperSpace L] [FiniteDimensional L V]
    (hh : IsHerm s h) (hδ : δ ≠ 0) (he : h e e = 0) (hf : h f f = 0) (hef : h e f = δ)
    (hU : ∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) {Λ : AddSubgroup V} (hΛ : IsLat L Λ) :
    IsLat L (Λ.comap U.subtype.toAddMonoidHom) := by sorry
