-- Prove2me | Theorems.Thm_GlobalTheory_T_antitone_powers_in_dominant_monoid
-- name    : GlobalTheory.T.antitone_powers_in_dominant_monoid
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:26:56.807796+00:00
-- url     : https://prove2.me/theorems/438cf239-c1c7-4f12-8738-b1e29395d7e4
-- title:
--   T: antitone powers in dominant monoid
-- statement:
--   The T construction uses the antitone powers in dominant monoid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntitonePowersInDominantMonoidStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/AntitonePowersInDominantMonoidStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntitonePowersInDominantMonoid
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntitonePowersInDominantMonoidStatement
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

theorem GlobalTheory.T.antitone_powers_in_dominant_monoid : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ) (a : Fin n → ℤ), Antitone a → GlobalTheory.CompanionTheory.CartGL.dPow p a ∈ Submonoid.closure (Set.range (GlobalTheory.CompanionTheory.CartGL.tGen p : Fin (n + 2) → GL (Fin n) L)) := by sorry
