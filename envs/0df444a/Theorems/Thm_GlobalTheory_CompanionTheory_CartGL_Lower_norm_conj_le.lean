-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_Lower_norm_conj_le
-- name    : GlobalTheory.CompanionTheory.CartGL.Lower.norm_conj_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:26:57.257452+00:00
-- url     : https://prove2.me/theorems/b82bc546-eda8-495d-b120-f415366a1a46
-- title:
--   Lower: norm conj le
-- statement:
--   The Lower construction uses the norm conj le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DominantConjugationPreservesLowerCongruence.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/DominantConjugationPreservesLowerCongruence.lean#L19-L30

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

theorem GlobalTheory.CompanionTheory.CartGL.Lower.norm_conj_le {L : Type} [NontriviallyNormedField L] (p : Lˣ) (hp : ‖(p : L)‖ < 1)
    {b c : ℤ} (hbc : b ≤ c) (x : L) :
    ‖((p ^ (-b) : Lˣ) : L) * x * ((p ^ c : Lˣ) : L)‖ ≤ ‖x‖ := by sorry
