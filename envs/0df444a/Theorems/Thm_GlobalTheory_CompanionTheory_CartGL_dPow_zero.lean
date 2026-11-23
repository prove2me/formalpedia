-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_zero
-- name    : GlobalTheory.CompanionTheory.CartGL.dPow_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:55.248152+00:00
-- url     : https://prove2.me/theorems/e3e50446-95e2-4aec-b1f6-e0ed7ee58adc
-- title:
--   Cart GL: d Pow zero
-- statement:
--   The Cart GL construction uses the d Pow zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/EntryMulSubOne.lean#L78-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/EntryMulSubOne.lean#L78-L80

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem GlobalTheory.CompanionTheory.CartGL.dPow_zero (p : Lˣ) : (dPow p (0 : Fin n → ℤ) : GL (Fin n) L) = 1 := by sorry
