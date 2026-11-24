-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_latOf_isLat
-- name    : GlobalTheory.CompanionTheory.RgSplit.latOf_isLat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:59:44.680866+00:00
-- url     : https://prove2.me/theorems/75ae7f3d-d58d-4150-bd9d-a71d5c3c51c2
-- title:
--   Rg Split: lat Of is Lat
-- statement:
--   The Rg Split construction uses the lat Of is Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/SplittingOfSandwichAndPairing.lean#L72-L73

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
variable [IsUltrametricDist L]

theorem GlobalTheory.CompanionTheory.RgSplit.latOf_isLat {m : ℕ} (b : Module.Basis (Fin m) L V) : IsLat L (latOf b) := by sorry
