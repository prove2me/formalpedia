-- Prove2me | Theorems.Thm_GlobalTheory_T_dominant_monoid_elements_are_antitone_powers
-- name    : GlobalTheory.T.dominant_monoid_elements_are_antitone_powers
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:32:28.826334+00:00
-- url     : https://prove2.me/theorems/b1425570-d622-4163-bbb6-2385a73d1739
-- title:
--   T: dominant monoid elements are antitone powers
-- statement:
--   The T construction uses the dominant monoid elements are antitone powers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DominantMonoidElementsAreAntitonePowersStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DominantMonoidElementsAreAntitonePowersStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantMonoidElementsAreAntitonePowers
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantMonoidElementsAreAntitonePowersStatement
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

theorem GlobalTheory.T.dominant_monoid_elements_are_antitone_powers : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ) (s : GL (Fin n) L), s ∈ Submonoid.closure (Set.range (GlobalTheory.CompanionTheory.CartGL.tGen p : Fin (n + 2) → GL (Fin n) L)) → ∃ a : Fin n → ℤ, Antitone a ∧ s = GlobalTheory.CompanionTheory.CartGL.dPow p a := by sorry
