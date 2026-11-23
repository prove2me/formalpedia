-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_herm_smul_left
-- name    : GlobalTheory.CompanionTheory.HermPlane.herm_smul_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:54:26.679186+00:00
-- url     : https://prove2.me/theorems/824cdbc5-4d79-4d7c-b8e1-079b7495fd9f
-- title:
--   Herm Plane: herm smul left
-- statement:
--   The Herm Plane construction uses the herm smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L140-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PlaneOfHenselAndPairing.lean#L140-L142

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

theorem GlobalTheory.CompanionTheory.HermPlane.herm_smul_left {s : L →+* L} {h : V → V → L} (hh : IsHerm s h) (a : L) (x y : V) :
    h (a • x) y = s a * h x y := by sorry
