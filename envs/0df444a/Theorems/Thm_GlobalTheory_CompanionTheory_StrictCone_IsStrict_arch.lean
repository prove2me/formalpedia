-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_StrictCone_IsStrict_arch
-- name    : GlobalTheory.CompanionTheory.StrictCone.IsStrict.arch
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:14:57.994192+00:00
-- url     : https://prove2.me/theorems/7dd3dd57-68e3-443d-92c6-415c540e49b5
-- title:
--   Is Strict: arch
-- statement:
--   The Is Strict construction uses the arch property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativeCharacterOnCone.lean#L96-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativeCharacterOnCone.lean#L96-L113

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativeCharacterOnCone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.StrictCone

theorem GlobalTheory.CompanionTheory.StrictCone.IsStrict.arch {n : ℕ} {s : Fin n → ℤ} (hs : IsStrict s) (g : Fin n → ℤ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → IsStrict (k • s + g) := by sorry
