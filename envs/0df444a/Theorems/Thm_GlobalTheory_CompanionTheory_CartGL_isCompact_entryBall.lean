-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_isCompact_entryBall
-- name    : GlobalTheory.CompanionTheory.CartGL.isCompact_entryBall
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:38.216576+00:00
-- url     : https://prove2.me/theorems/6f739411-d468-43b6-9b5d-71c6765c9b30
-- title:
--   Cart GL: is Compact entry Ball
-- statement:
--   The Cart GL construction uses the is Compact entry Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupIsCompact.lean#L8-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupIsCompact.lean#L8-L27

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL

theorem GlobalTheory.CompanionTheory.CartGL.isCompact_entryBall (L : Type) [NontriviallyNormedField L] [ProperSpace L] (n : ℕ) (r : ℝ) :
    IsCompact {M : Matrix (Fin n) (Fin n) L | ∀ i j, ‖(M - 1) i j‖ ≤ r} := by sorry
