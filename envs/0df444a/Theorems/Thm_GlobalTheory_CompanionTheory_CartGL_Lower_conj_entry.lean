-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_Lower_conj_entry
-- name    : GlobalTheory.CompanionTheory.CartGL.Lower.conj_entry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:26:56.226556+00:00
-- url     : https://prove2.me/theorems/b13e69a0-716e-4b92-82d9-91adef548401
-- title:
--   Lower: conj entry
-- statement:
--   The Lower construction uses the conj entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DominantConjugationPreservesLowerCongruence.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DominantConjugationPreservesLowerCongruence.lean#L10-L17

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantConjugationPreservesLowerCongruence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL GlobalTheory.CompanionTheory.CartGL.Lower

theorem GlobalTheory.CompanionTheory.CartGL.Lower.conj_entry {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
    (p : Lˣ) (a : Fin n → ℤ) (w : GL (Fin n) L) (i j : Fin n) :
    (((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) i j =
      ((p ^ (-a i) : Lˣ) : L) * (w : Matrix (Fin n) (Fin n) L) i j * ((p ^ a j : Lˣ) : L) := by sorry
