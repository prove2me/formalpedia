-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_exists_isUnif
-- name    : GlobalTheory.CompanionTheory.CartGL.exists_isUnif
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:26:58.749589+00:00
-- url     : https://prove2.me/theorems/9444b971-99d1-4d18-aa83-77361e82c281
-- title:
--   Cart GL: exists is Unif
-- statement:
--   The Cart GL construction uses the exists is Unif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsUniformizerNonarchimedean.lean#L8-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/ExistsUniformizerNonarchimedean.lean#L8-L42

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsUniformizerNonarchimedean
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

theorem GlobalTheory.CompanionTheory.CartGL.exists_isUnif : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L],
    ∃ p : Lˣ, GlobalTheory.CompanionTheory.CartGL.IsUnif p := by sorry
