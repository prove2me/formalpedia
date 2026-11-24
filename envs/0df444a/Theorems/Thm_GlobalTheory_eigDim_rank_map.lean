-- Prove2me | Theorems.Thm_GlobalTheory_eigDim_rank_map
-- name    : GlobalTheory.eigDim_rank_map
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:34.905497+00:00
-- url     : https://prove2.me/theorems/afb1377a-0a8b-4868-8a0f-217df0af951d
-- title:
--   Global Theory: eig Dim rank map
-- statement:
--   The Global Theory construction uses the eig Dim rank map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl.lean#L19-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl.lean#L19-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
open Matrix

theorem GlobalTheory.eigDim_rank_map {K L : Type} [Field K] [Field L] (φ : K →+* L) {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) : (M.map φ).rank = M.rank := by sorry
