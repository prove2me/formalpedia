-- Prove2me | Theorems.Thm_GlobalTheory_T_congruence_subgroup_is_open
-- name    : GlobalTheory.T.congruence_subgroup_is_open
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:32:49.346445+00:00
-- url     : https://prove2.me/theorems/dd1eb1a1-a923-4fa7-80d9-b4079f561b40
-- title:
--   T: congruence subgroup is open
-- statement:
--   The T construction uses the congruence subgroup is open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupIsOpenStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupIsOpenStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupIsOpen
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupIsOpenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.congruence_subgroup_is_open : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), 0 < r → IsOpen (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by sorry
