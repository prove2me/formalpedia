-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_hyperbolic_partner
-- name    : GlobalTheory.CompanionTheory.HermPlane.hyperbolic_partner
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:14.835999+00:00
-- url     : https://prove2.me/theorems/80c4dbcf-4ab7-4129-861a-1a78386a7434
-- title:
--   Herm Plane: hyperbolic partner
-- statement:
--   The Herm Plane construction uses the hyperbolic partner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L190-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L190-L223

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

theorem GlobalTheory.CompanionTheory.HermPlane.hyperbolic_partner {s : L →+* L} (hs : IsInv s) {δ : L} (hδ : IsDelta s δ) {h : V → V → L}
    (hh : IsHerm s h) {e y : V} (he : h e e = 0) (hqy : ‖h y y‖ ≤ 1) (hey : ‖h e y‖ = ‖δ‖) :
    ∃ b t : L, ‖b‖ = 1 ∧ ‖t‖ ≤ 1 ∧ h (b • y + t • e) (b • y + t • e) = 0 ∧
      h e (b • y + t • e) = δ := by sorry
