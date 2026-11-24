-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_mem_closure_of_ge
-- name    : GlobalTheory.CompanionTheory.CartGL.dPow_mem_closure_of_ge
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:07.647095+00:00
-- url     : https://prove2.me/theorems/5c0bceba-585e-4de6-bf89-cbc2c35bba85
-- title:
--   Cart GL: d Pow mem closure of ge
-- statement:
--   The Cart GL construction uses the d Pow mem closure of ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntitonePowersInDominantMonoid.lean#L77-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntitonePowersInDominantMonoid.lean#L77-L112

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

theorem GlobalTheory.CompanionTheory.CartGL.dPow_mem_closure_of_ge (p : Lˣ) (C : ℕ) :
    ∀ a : Fin n → ℤ, Antitone a → (∀ j, -(C : ℤ) ≤ a j) →
      dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by sorry
