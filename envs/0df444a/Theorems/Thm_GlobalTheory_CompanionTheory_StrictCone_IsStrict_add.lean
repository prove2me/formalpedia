-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_StrictCone_IsStrict_add
-- name    : GlobalTheory.CompanionTheory.StrictCone.IsStrict.add
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:45.654906+00:00
-- url     : https://prove2.me/theorems/9edb8c91-39c1-48c6-acae-6178c6622836
-- title:
--   Is Strict: add
-- statement:
--   The Is Strict construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativeCharacterOnCone.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativeCharacterOnCone.lean#L88-L94

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

theorem GlobalTheory.CompanionTheory.StrictCone.IsStrict.add {n : ℕ} {x y : Fin n → ℤ} (hx : IsStrict x) (hy : IsStrict y) :
    IsStrict (x + y) := by sorry
