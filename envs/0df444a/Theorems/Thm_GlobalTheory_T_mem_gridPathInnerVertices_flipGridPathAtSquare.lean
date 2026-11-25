-- Prove2me | Theorems.Thm_GlobalTheory_T_mem_gridPathInnerVertices_flipGridPathAtSquare
-- name    : GlobalTheory.T.mem_gridPathInnerVertices_flipGridPathAtSquare
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:35:19.855976+00:00
-- url     : https://prove2.me/theorems/646a8018-e5db-5671-a31d-fc7317022a12
-- title:
--   T: mem grid Path Inner Vertices flip Grid Path At Square
-- statement:
--   The T construction uses the mem grid Path Inner Vertices flip Grid Path At Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemGridPathInnerVerticesFlipGridPathAtSquareStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/MemGridPathInnerVerticesFlipGridPathAtSquareStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemGridPathInnerVerticesFlipGridPathAtSquare
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemGridPathInnerVerticesFlipGridPathAtSquareStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mem_gridPathInnerVertices_flipGridPathAtSquare : ∀ {γ : List Edge} {i j : ℕ}, IsPath γ → PassesThrough i j γ → ∀ X ∈ innerVertices (flipPath i j γ), X ≠ (i, j) ∧ (X ≠ (i + 1, j + 1) → X ∈ innerVertices γ) := by sorry
