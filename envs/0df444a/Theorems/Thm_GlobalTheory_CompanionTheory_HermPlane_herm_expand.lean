-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_herm_expand
-- name    : GlobalTheory.CompanionTheory.HermPlane.herm_expand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:54.741377+00:00
-- url     : https://prove2.me/theorems/83051c8f-e3f9-4a59-afd3-319c6b73d3df
-- title:
--   Herm Plane: herm expand
-- statement:
--   The Herm Plane construction uses the herm expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L144-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L144-L149

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

theorem GlobalTheory.CompanionTheory.HermPlane.herm_expand {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (a c : L) (x y : V) :
    h (c • x + a • y) (c • x + a • y) =
      s c * (c * h x x) + s c * (a * h x y) + s a * (c * h y x) + s a * (a * h y y) := by sorry
