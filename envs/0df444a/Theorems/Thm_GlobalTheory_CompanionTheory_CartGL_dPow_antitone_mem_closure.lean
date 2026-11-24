-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_antitone_mem_closure
-- name    : GlobalTheory.CompanionTheory.CartGL.dPow_antitone_mem_closure
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:26.532724+00:00
-- url     : https://prove2.me/theorems/b851728c-70ba-42cd-844c-ced69c19420f
-- title:
--   Cart GL: d Pow antitone mem closure
-- statement:
--   The Cart GL construction uses the d Pow antitone mem closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntitonePowersInDominantMonoid.lean#L114-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntitonePowersInDominantMonoid.lean#L114-L121

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntitonePowersInDominantMonoid
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
variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem GlobalTheory.CompanionTheory.CartGL.dPow_antitone_mem_closure (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
    (n : ℕ) (p : Lˣ) (a : Fin n → ℤ) (ha : Antitone a) :
    dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by sorry
