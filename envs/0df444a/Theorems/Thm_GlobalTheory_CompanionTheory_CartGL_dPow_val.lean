-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_val
-- name    : GlobalTheory.CompanionTheory.CartGL.dPow_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:51:40.084295+00:00
-- url     : https://prove2.me/theorems/d63b350c-e08d-4dc8-8173-c6d061d926aa
-- title:
--   Cart GL: d Pow val
-- statement:
--   The Cart GL construction uses the d Pow val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/EntryMulSubOne.lean#L68-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/EntryMulSubOne.lean#L68-L69

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

theorem GlobalTheory.CompanionTheory.CartGL.dPow_val (p : Lˣ) (a : Fin n → ℤ) :
    ((dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = diagonal fun i => ((p ^ a i : Lˣ) : L) := by sorry
