-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_conj_upper_contract
-- name    : GlobalTheory.CompanionTheory.CartGL.conj_upper_contract
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:27:15.97696+00:00
-- url     : https://prove2.me/theorems/8bdcce65-4466-4d30-bcf3-7883fa9360a7
-- title:
--   Cart GL: conj upper contract
-- statement:
--   The Cart GL construction uses the conj upper contract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DominantConjugationPreservesUpperCongruence.lean#L8-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DominantConjugationPreservesUpperCongruence.lean#L8-L38

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantConjugationPreservesUpperCongruence
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

theorem GlobalTheory.CompanionTheory.CartGL.conj_upper_contract : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (u : GL (Fin n) L), (∀ i j, j < i → (u : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((u : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖(((GlobalTheory.CompanionTheory.CartGL.dPow p a * u * (GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by sorry
