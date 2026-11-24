-- Prove2me | Theorems.Thm_GlobalTheory_SplitFlip_IsPath_eq_of_src_eq_of_mem
-- name    : GlobalTheory.SplitFlip.IsPath.eq_of_src_eq_of_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:20:46.809801+00:00
-- url     : https://prove2.me/theorems/6d5d8543-de6e-4a6c-87c0-4773aea09e9c
-- title:
--   Is Path: eq of src eq of mem
-- statement:
--   The Is Path construction uses the eq of src eq of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemGridPathInnerVerticesFlipGridPathAtSquare.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemGridPathInnerVerticesFlipGridPathAtSquare.lean#L19-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemGridPathInnerVerticesFlipGridPathAtSquare
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SplitFlip

theorem GlobalTheory.SplitFlip.IsPath.eq_of_src_eq_of_mem {γ : List Edge} (hγ : IsPath γ) {a b : Edge} (ha : a ∈ γ) (hb : b ∈ γ)
    (h : a.src = b.src) : a = b := by sorry
