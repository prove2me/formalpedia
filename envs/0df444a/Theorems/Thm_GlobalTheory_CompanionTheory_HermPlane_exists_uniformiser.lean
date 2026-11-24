-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_exists_uniformiser
-- name    : GlobalTheory.CompanionTheory.HermPlane.exists_uniformiser
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:21.014905+00:00
-- url     : https://prove2.me/theorems/3f475144-5dda-4024-8deb-b5e8bd92d95f
-- title:
--   Herm Plane: exists uniformiser
-- statement:
--   The Herm Plane construction uses the exists uniformiser property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L14-L28

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermPlane
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {V : Type} [AddCommGroup V] [Module L V]

theorem GlobalTheory.CompanionTheory.HermPlane.exists_uniformiser [ProperSpace L] :
    ∃ p : L, p ≠ 0 ∧ ‖p‖ < 1 ∧ ∀ a : L, ‖a‖ < 1 → ‖a‖ ≤ ‖p‖ := by sorry
