-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_tExp_antitone
-- name    : GlobalTheory.CompanionTheory.CartGL.tExp_antitone
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:27:19.111054+00:00
-- url     : https://prove2.me/theorems/e4400999-f441-4481-b6bd-5bbfde9d1403
-- title:
--   Cart GL: t Exp antitone
-- statement:
--   The Cart GL construction uses the t Exp antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DominantMonoidElementsAreAntitonePowers.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DominantMonoidElementsAreAntitonePowers.lean#L8-L18

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantMonoidElementsAreAntitonePowers
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

theorem GlobalTheory.CompanionTheory.CartGL.tExp_antitone (n : ℕ) (i : Fin (n + 2)) : Antitone (tExp n i) := by sorry
