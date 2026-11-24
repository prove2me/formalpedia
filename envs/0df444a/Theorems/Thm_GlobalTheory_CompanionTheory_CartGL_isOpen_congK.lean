-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_isOpen_congK
-- name    : GlobalTheory.CompanionTheory.CartGL.isOpen_congK
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:36.844412+00:00
-- url     : https://prove2.me/theorems/b570675c-47b6-4876-b466-de14d8769cd4
-- title:
--   Cart GL: is Open cong K
-- statement:
--   The Cart GL construction uses the is Open cong K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupIsOpen.lean#L8-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CongruenceSubgroupIsOpen.lean#L8-L33

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupIsOpen
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

theorem GlobalTheory.CompanionTheory.CartGL.isOpen_congK : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1), 0 < r →
    IsOpen (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by sorry
