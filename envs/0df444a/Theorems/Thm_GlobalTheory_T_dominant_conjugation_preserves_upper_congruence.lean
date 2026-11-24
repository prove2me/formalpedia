-- Prove2me | Theorems.Thm_GlobalTheory_T_dominant_conjugation_preserves_upper_congruence
-- name    : GlobalTheory.T.dominant_conjugation_preserves_upper_congruence
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:32:58.273723+00:00
-- url     : https://prove2.me/theorems/d7ab1aad-00d7-41f5-8cc3-d51f3778f80e
-- title:
--   T: dominant conjugation preserves upper congruence
-- statement:
--   The T construction uses the dominant conjugation preserves upper congruence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DominantConjugationPreservesUpperCongruenceStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DominantConjugationPreservesUpperCongruenceStatement.lean#L6-L7

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantConjugationPreservesUpperCongruence
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantConjugationPreservesUpperCongruenceStatement
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

theorem GlobalTheory.T.dominant_conjugation_preserves_upper_congruence : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (u : GL (Fin n) L), (∀ i j, j < i → (u : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((u : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖(((GlobalTheory.CompanionTheory.CartGL.dPow p a * u * (GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by sorry
