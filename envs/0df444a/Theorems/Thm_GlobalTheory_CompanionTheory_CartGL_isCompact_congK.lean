-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_isCompact_congK
-- name    : GlobalTheory.CompanionTheory.CartGL.isCompact_congK
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:11.750659+00:00
-- url     : https://prove2.me/theorems/84bb6b38-8492-45d6-8603-a720d921a4f2
-- title:
--   Cart GL: is Compact cong K
-- statement:
--   The Cart GL construction uses the is Compact cong K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupIsCompact.lean#L29-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupIsCompact.lean#L29-L45

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

theorem GlobalTheory.CompanionTheory.CartGL.isCompact_congK (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    IsCompact (congK L n r h0 h1 : Set (GL (Fin n) L)) := by sorry
