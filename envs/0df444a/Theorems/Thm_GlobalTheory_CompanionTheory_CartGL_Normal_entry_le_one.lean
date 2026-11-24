-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_Normal_entry_le_one
-- name    : GlobalTheory.CompanionTheory.CartGL.Normal.entry_le_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:55.216205+00:00
-- url     : https://prove2.me/theorems/a0bd2449-395e-46c1-bf8a-eb76dfde6901
-- title:
--   Normal: entry le one
-- statement:
--   The Normal construction uses the entry le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupNormalInMaximalCompact.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupNormalInMaximalCompact.lean#L10-L19

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupNormalInMaximalCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.Normal
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem GlobalTheory.CompanionTheory.CartGL.Normal.entry_le_one {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖(A - 1) i j‖ ≤ 1) (i j : Fin n) :
    ‖A i j‖ ≤ 1 := by sorry
